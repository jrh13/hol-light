#!/usr/bin/env python3
"""MCP server for HOL Light theorem prover."""

import asyncio
from concurrent.futures import ThreadPoolExecutor
import json
import os
import queue
import re
import shutil
import subprocess
import sys
import tempfile
import threading
import time

HOL_DIR = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
MCP_DIR = os.path.dirname(os.path.abspath(__file__))
SENTINEL = "HOL_MCP_DONE_a7f3b2e1"
ANSI_RE = re.compile(r"\x1b\[[0-9;]*m")
CHECKPOINT_RE = re.compile(r"^[A-Za-z0-9][A-Za-z0-9_.-]*$")
RESTART_HEARTBEAT_SECONDS = 15


def _load_config():
    """Load config from hol-mcp.toml. Search order:
    1. --config CLI arg  2. HOL_MCP_CONFIG env  3. CWD  4. MCP_DIR"""
    import tomllib
    config_path = None
    for i, arg in enumerate(sys.argv):
        if arg == "--config" and i + 1 < len(sys.argv):
            config_path = sys.argv[i + 1]
            break
    if not config_path:
        config_path = os.environ.get("HOL_MCP_CONFIG")
    if not config_path:
        for d in [os.getcwd(), MCP_DIR]:
            p = os.path.join(d, "hol-mcp.toml")
            if os.path.isfile(p):
                config_path = p
                break
    if config_path and os.path.isfile(config_path):
        with open(config_path, "rb") as f:
            return tomllib.load(f), os.path.abspath(config_path)
    return {}, None


_config, CONFIG_PATH = _load_config()


def _positive_int(value, name):
    if isinstance(value, bool) or not isinstance(value, int) or value <= 0:
        raise ValueError(f"{name} must be a positive integer")
    return value


def _optional_string(value, name):
    if value is not None and not isinstance(value, str):
        raise ValueError(f"{name} must be a string")
    return value


def _validate_checkpoint_name(name):
    if not isinstance(name, str) or not CHECKPOINT_RE.fullmatch(name) or ".." in name:
        raise ValueError(
            "checkpoint must start with an alphanumeric character and contain "
            "only letters, digits, '.', '_', or '-'"
        )
    return name


def _effective_config(config, config_path):
    """Validate raw TOML data and return its effective runtime values."""
    if not isinstance(config, dict):
        raise ValueError("configuration root must be a TOML table")

    checkpoint = _validate_checkpoint_name(
        config.get("checkpoint", os.environ.get("HOL_CHECKPOINT", "base"))
    )
    timeout = _positive_int(
        config.get("timeout", int(os.environ.get("HOL_TIMEOUT", "600"))),
        "timeout",
    )
    max_output = _positive_int(
        config.get(
            "max_output_chars", int(os.environ.get("HOL_MAX_OUTPUT", "4000"))
        ),
        "max_output_chars",
    )

    recording_dir = config.get("recording_dir") or os.environ.get(
        "HOL_RECORDING_DIR"
    )
    recording_dir = _optional_string(recording_dir, "recording_dir")
    if recording_dir:
        recording_dir = os.path.abspath(recording_dir)

    replay_init = _optional_string(
        config.get("replay_init") or os.environ.get("HOL_REPLAY_INIT"),
        "replay_init",
    )
    replay_prefix = _optional_string(
        config.get("replay_prefix") or os.environ.get("HOL_REPLAY_PREFIX"),
        "replay_prefix",
    )

    raw_recipes = config.get("checkpoint_recipes", {})
    if not isinstance(raw_recipes, dict):
        raise ValueError("checkpoint_recipes must be a TOML table")
    config_dir = os.path.dirname(config_path) if config_path else os.getcwd()
    recipes = {}
    for name, raw_recipe in raw_recipes.items():
        _validate_checkpoint_name(name)
        if not isinstance(raw_recipe, dict):
            raise ValueError(f"checkpoint_recipes.{name} must be a TOML table")
        include_dirs = raw_recipe.get("include_dirs", [])
        loads = raw_recipe.get("loads", [])
        if (
            not isinstance(include_dirs, list)
            or not all(isinstance(path, str) for path in include_dirs)
        ):
            raise ValueError(
                f"checkpoint_recipes.{name}.include_dirs must be an array of strings"
            )
        if (
            not isinstance(loads, list)
            or not all(isinstance(load, str) for load in loads)
        ):
            raise ValueError(
                f"checkpoint_recipes.{name}.loads must be an array of strings"
            )
        recipes[name] = {
            "include_dirs": [
                path
                if os.path.isabs(path)
                else os.path.abspath(os.path.join(config_dir, path))
                for path in include_dirs
            ],
            "loads": list(loads),
        }

    return {
        "raw": config,
        "checkpoint": checkpoint,
        "timeout": timeout,
        "max_output_chars": max_output,
        "recording_dir": recording_dir,
        "replay_init": replay_init,
        "replay_prefix": replay_prefix,
        "checkpoint_recipes": recipes,
    }


def _config_snapshot(config):
    return {
        key: config[key]
        for key in (
            "checkpoint",
            "timeout",
            "max_output_chars",
            "recording_dir",
            "replay_init",
            "replay_prefix",
            "checkpoint_recipes",
        )
    }


_runtime_config = _effective_config(_config, CONFIG_PATH)
TIMEOUT = _runtime_config["timeout"]
CONFIGURED_CHECKPOINT = _runtime_config["checkpoint"]
CHECKPOINT_NAME = CONFIGURED_CHECKPOINT
MAX_OUTPUT_CHARS = _runtime_config["max_output_chars"]

from mcp.server.fastmcp import Context, FastMCP
mcp = FastMCP("hol-light",
    instructions="HOL Light theorem prover. Call hol_help() for a tactic reference and proof guide.")


def _read_skill():
    path = os.path.join(MCP_DIR, "SKILL.md")
    if os.path.isfile(path):
        with open(path) as f:
            return f.read()
    return "SKILL.md not found."

_proc = None
_lock = threading.Lock()
_restart_lock = threading.Lock()
_helpers_loaded = False
_start_time = None
_startup_mode = None
_checkpoint_active = False
_checkpoint_error = None
_checkpoint_fingerprint = None
_restart_required = False
_restart_error = None

# Proof recording state
_recording_path = None  # path to JSONL file; None = not recording
_recording = []         # list of {"action": "tactic", "tactic": ..., "total_goals": ...}

# Auto-recording: if recording_dir is set in config or env, enable recording at startup.
_auto_record_dir = _runtime_config["recording_dir"]
if _auto_record_dir:
    os.makedirs(_auto_record_dir, exist_ok=True)
    _recording_path = os.path.join(_auto_record_dir, "recording.jsonl")

# Queue-based sentinel signaling: reader thread produces results, eval consumes.
# Eliminates race conditions — queue.get() is atomic consumption.
_result_queue = queue.Queue(maxsize=1)
_reader_buf = []


def _reader_thread(proc, result_queue, reader_buf):
    while True:
        line = proc.stdout.readline()
        if not line:
            # Process died — signal immediately so callers don't hang
            result_queue.put("[HOL Light process died unexpectedly]")
            break
        if SENTINEL in line:
            result_queue.put("".join(reader_buf).strip())
            reader_buf.clear()
        else:
            reader_buf.append(line)


def _opam_env():
    env = os.environ.copy()
    # Ensure DMTCP can find libatomic
    ld_path = os.path.expanduser("~/.local/lib")
    if os.path.isdir(ld_path):
        env["LD_LIBRARY_PATH"] = ld_path + ":" + env.get("LD_LIBRARY_PATH", "")
    if not os.path.isdir(os.path.join(HOL_DIR, "_opam")):
        return env
    try:
        r = subprocess.run(
            ["opam", "env", "--switch", HOL_DIR + "/", "--set-switch"],
            capture_output=True, text=True,
        )
        for line in r.stdout.strip().split("\n"):
            if "=" in line and "'" in line:
                key = line.split("=", 1)[0].strip()
                val = line.split("'")[1]
                env[key] = val
    except FileNotFoundError:
        pass
    return env


def _checkpoint_dir(name):
    return os.path.join(HOL_DIR, f"hol-{name}.ckpt")


def _checkpoint_files(name):
    ckpt_dir = _checkpoint_dir(name)
    if not os.path.isdir(ckpt_dir):
        return []
    return sorted(
        os.path.join(ckpt_dir, filename)
        for filename in os.listdir(ckpt_dir)
        if filename.startswith("ckpt_") and filename.endswith(".dmtcp")
    )


def _fingerprint_checkpoint(name):
    fingerprint = []
    for path in _checkpoint_files(name):
        try:
            stat = os.stat(path)
        except OSError:
            return None
        fingerprint.append(
            {
                "name": os.path.basename(path),
                "size": stat.st_size,
                "mtime_ns": stat.st_mtime_ns,
            }
        )
    return fingerprint or None


def _start_hol(
    checkpoint=None,
    force_cold=False,
    checkpoint_error=None,
    allow_restart_required=False,
):
    global _proc, _result_queue, _reader_buf
    global _start_time, _startup_mode, _checkpoint_active
    global _checkpoint_error, _checkpoint_fingerprint, CHECKPOINT_NAME
    if _restart_required and not allow_restart_required:
        raise RuntimeError(
            f"HOL is unavailable after a failed HOL/checkpoint rebuild: {_restart_error}. "
            "Fix the build and run hol_restart(rebuild_hol_and_checkpoint=true)."
        )
    if _proc is not None:
        return
    checkpoint = checkpoint or CHECKPOINT_NAME
    CHECKPOINT_NAME = checkpoint
    ckpt_files = _checkpoint_files(checkpoint)
    use_checkpoint = bool(ckpt_files) and not force_cold
    _checkpoint_fingerprint = _fingerprint_checkpoint(checkpoint)
    _checkpoint_active = use_checkpoint
    _startup_mode = "checkpoint" if use_checkpoint else "cold"
    if checkpoint_error:
        _checkpoint_error = checkpoint_error
    elif not ckpt_files:
        _checkpoint_error = (
            f"No usable checkpoint files found in {_checkpoint_dir(checkpoint)}"
        )
    else:
        _checkpoint_error = None

    _result_queue = queue.Queue(maxsize=1)
    _reader_buf = []
    if use_checkpoint:
        _proc = subprocess.Popen(
            ["dmtcp_restart", "--no-strict-checking", "--coord-port", "0"] +
            ckpt_files,
            stdin=subprocess.PIPE,
            stdout=subprocess.PIPE,
            stderr=subprocess.STDOUT,
            cwd=HOL_DIR,
            text=True,
            bufsize=1,
            env=_opam_env(),
        )
    else:
        _proc = subprocess.Popen(
            [os.path.join(HOL_DIR, "ocaml-hol"), "-init",
             os.path.join(HOL_DIR, "hol.ml"), "-I", HOL_DIR],
            stdin=subprocess.PIPE,
            stdout=subprocess.PIPE,
            stderr=subprocess.STDOUT,
            cwd=HOL_DIR,
            text=True,
            bufsize=1,
            env=_opam_env(),
        )
    _start_time = time.time()
    t = threading.Thread(
        target=_reader_thread,
        args=(_proc, _result_queue, _reader_buf),
        daemon=True,
    )
    t.start()


def _wait_for_sentinel(timeout=None):
    if timeout is None:
        timeout = TIMEOUT
    try:
        return _result_queue.get(timeout=timeout)
    except queue.Empty:
        return "[timeout waiting for HOL Light response]"


def _drain_queue():
    """Discard any stale results in the queue."""
    while not _result_queue.empty():
        try:
            _result_queue.get_nowait()
        except queue.Empty:
            break


def _load_helpers():
    global _helpers_loaded
    if _helpers_loaded:
        return
    helpers_path = os.path.join(MCP_DIR, "mcp_helpers.ml")
    _drain_queue()
    _reader_buf.clear()
    cmd = f'#use "{helpers_path}";;\nPrintf.printf "{SENTINEL}\\n%!";;\n'
    _proc.stdin.write(cmd)
    _proc.stdin.flush()
    result = _wait_for_sentinel()
    if "MCP helpers loaded" in result:
        _helpers_loaded = True
    else:
        raise RuntimeError(f"Failed to load MCP helpers: {result}")
    _replay_prefix()


def _replay_prefix():
    """Replay a tactic prefix on startup to restore proof state.

    Loads replay_init (ML file) then replays replay_prefix (JSONL of tactics).
    Both are optional; configured via hol-mcp.toml or env vars.
    """
    init_path = _runtime_config["replay_init"]
    prefix_path = _runtime_config["replay_prefix"]
    if not init_path and not prefix_path:
        return
    if init_path:
        result, _ = _eval_raw(f'#use "{_ocaml_escape(init_path)}"')
        if _is_error_output(_strip_ansi(result)):
            return
    if not prefix_path or not os.path.exists(prefix_path):
        return
    import json
    replayed = []
    try:
        with open(prefix_path) as f:
            for line in f:
                line = line.strip()
                if not line:
                    continue
                entry = json.loads(line)
                if entry.get("action") == "backtrack":
                    steps = entry.get("steps", 1)
                    removed = 0
                    while removed < steps and replayed:
                        replayed.pop()
                        _eval_raw("b()")
                        removed += 1
                elif entry.get("action") == "tactic":
                    result, _ = _eval_raw(f'e({entry["tactic"]})')
                    if _is_error_output(_strip_ansi(result)):
                        for _ in range(len(replayed)):
                            _eval_raw("b()")
                        return
                    replayed.append(entry)
    except (json.JSONDecodeError, KeyError, OSError):
        for _ in range(len(replayed)):
            _eval_raw("b()")
        return
    global _recording, _recording_flushed
    _recording = replayed
    _recording_flushed = len(replayed)  # entries already on disk


def _eval_raw(code: str, timeout: int = None) -> tuple[str, float]:
    """Eval code, return (output, elapsed_seconds). Caller must hold _lock."""
    _drain_queue()
    _reader_buf.clear()
    full = code.rstrip()
    if not full.endswith(";;"):
        full += ";;"
    full += f'\nPrintf.printf "{SENTINEL}\\n%!";;\n'
    t0 = time.time()
    _proc.stdin.write(full)
    _proc.stdin.flush()
    result = _wait_for_sentinel(timeout)
    return result, round(time.time() - t0, 3)


def _eval_code(code: str, timeout: int = None) -> tuple[str, float]:
    with _lock:
        _start_hol()
        _load_helpers()
        return _eval_raw(code, timeout)


def _eval_json(code: str, timeout: int = None) -> tuple[str, float]:
    """Eval OCaml code that produces a string, print it to stdout, return it.
    Uses print_string to avoid OCaml's string truncation in REPL output."""
    return _eval_code(f'print_string ({code}); print_newline ()', timeout)


def _strip_ansi(s: str) -> str:
    return ANSI_RE.sub("", s)


def _truncate(s: str, limit: int) -> tuple[str, bool]:
    """Truncate string to limit chars. Returns (result, was_truncated)."""
    if len(s) <= limit:
        return s, False
    return s[:limit] + "... [truncated]", True


def _is_error_output(s: str) -> bool:
    """Heuristic: check if OCaml output indicates an error."""
    for marker in ("Error:", "Exception:", "Failure", "Unbound", "Parse error",
                   "Syntax error", "Type error", "This expression has type"):
        if marker in s:
            return True
    return False


@mcp.tool()
def eval(code: str, timeout: int = None, max_output_chars: int = None) -> str:
    """Evaluate OCaml/HOL Light code and return structured JSON.

    Args:
        code: OCaml/HOL Light code to evaluate.
        timeout: Optional timeout in seconds.
        max_output_chars: Max chars for output field (default from config, typically 4000).

    Returns JSON:
        {"success": bool, "output": str, "output_truncated": bool,
         "full_output_chars": int, "time_seconds": float}
    """
    import json as _json
    # Detect recording patterns before eval
    is_bt = _is_backtrack(code) if _recording_path else None
    tac = _extract_e_tactic(code) if (_recording_path and not is_bt) else None

    with _lock:
        _start_hol()
        _load_helpers()
        raw, elapsed = _eval_raw(code, timeout)
        raw = _strip_ansi(raw)
        # Record e(...) and b() calls while still holding the lock
        if _recording_path:
            if is_bt:
                _record_backtrack(1)
            elif tac and not _is_error_output(raw):
                gs_raw, _ = _eval_raw("print_string (mcp_json_after_tactic ()); print_newline ()")
                _record_tactic(tac, _extract_json(gs_raw))

    limit = max_output_chars if max_output_chars is not None else MAX_OUTPUT_CHARS
    full_len = len(raw)
    output, truncated = _truncate(raw, limit)
    return _json.dumps({
        "success": not _is_error_output(raw),
        "output": output,
        "output_truncated": truncated,
        "full_output_chars": full_len,
        "time_seconds": elapsed,
    })


@mcp.tool()
def goal_state() -> str:
    """Return the current goal state as JSON.

    Returns JSON: {"goals": [{"hypotheses": [...], "conclusion": "..."}],
                   "num_subgoals": N, "total_goals": M}
    Returns empty goals list if no proof is in progress.
    """
    return _extract_json(_eval_json("mcp_json_goalstate ()")[0])


@mcp.tool()
def apply_tactic(tactic: str, timeout: int = None) -> str:
    """Apply a tactic to the current goal and return the resulting state as JSON.

    The tactic should be a valid HOL Light tactic expression, e.g.:
        ARITH_TAC
        GEN_TAC THEN REWRITE_TAC[ADD]
        MESON_TAC[]

    Returns JSON with either:
      - New goal state: {"goals": [...], "num_subgoals": N, "total_goals": M}
      - Proof complete: {"proved": true, "theorem": "..."}
      - Error: {"error": "..."}
    """
    code = (f'(try ignore(e({tactic})); '
            f'print_string (mcp_json_after_tactic ()) '
            f'with Failure s -> print_string (mcp_json_error s) '
            f'| e -> print_string (mcp_json_error (Printexc.to_string e))); '
            f'print_newline ()')
    with _lock:
        _start_hol()
        _load_helpers()
        result = _extract_json(_eval_raw(code, timeout)[0])
        _record_tactic(tactic, result)
    return result


@mcp.tool()
def apply_tactics(tactics: list[str], timeout: int = None) -> str:
    """Apply a list of tactics sequentially in a single round-trip.

    Stops at the first error or when the proof is complete.

    Args:
        tactics: List of HOL Light tactic expressions.
        timeout: Optional timeout in seconds for the entire batch.

    Returns JSON with:
      - Proof complete: {"proved": true, "theorem": "...", "steps": N}
      - Error: {"error": "...", "step": N}
      - Goal state after all tactics: goal state JSON with added "steps" field
    """
    if not tactics:
        return '{"error":"empty tactic list"}'
    tac_list = "[" + "; ".join(tactics) + "]"
    code = (f'print_string (mcp_json_apply_tactics {tac_list}); print_newline ()')
    with _lock:
        _start_hol()
        _load_helpers()
        result = _extract_json(_eval_raw(code, timeout)[0])
        _record_tactics_batch(tactics, result)
    return result


@mcp.tool()
def prove(goal: str, tactic: str, timeout: int = None) -> str:
    """Prove a theorem in one shot using a goal and tactic.

    This is a convenience wrapper around HOL Light's prove() function.
    Use for simple proofs that don't need interactive stepping.

    Args:
        goal: HOL Light term to prove (e.g., "`!n. n + 0 = n`")
        tactic: Complete tactic to prove the goal (e.g., "GEN_TAC THEN ARITH_TAC")
        timeout: Optional timeout in seconds.

    Returns JSON:
      - Success: {"proved": true, "theorem": "..."}
      - Error: {"error": "..."}
    """
    code = (f'(try let th = prove({goal}, {tactic}) in '
            f'print_string ("{{\\"proved\\":true,\\"theorem\\":" ^ '
            f'mcp_json_string (string_of_thm th) ^ "}}") '
            f'with Failure s -> print_string (mcp_json_error s) '
            f'| e -> print_string (mcp_json_error (Printexc.to_string e))); '
            f'print_newline ()')
    return _extract_json(_eval_code(code, timeout)[0])


@mcp.tool()
def backtrack(steps: int = 1) -> str:
    """Undo tactic steps and return the resulting goal state as JSON.

    Args:
        steps: Number of steps to undo (default 1).

    Returns JSON goal state or {"error": "..."} if can't back up.
    """
    with _lock:
        _start_hol()
        _load_helpers()
        result = _extract_json(_eval_raw(f'print_string (mcp_json_backtrack {steps}); print_newline ()')[0])
        _record_backtrack(steps)
    return result


@mcp.tool()
def search_theorems(name: str, limit: int = 20) -> str:
    """Search the theorem database by name and return results as JSON.

    Args:
        name: Substring to search for in theorem names.
        limit: Maximum results to return (default 20).

    Returns JSON array: [{"name": "...", "statement": "..."}, ...]
    """
    return _extract_json(_eval_json(f'mcp_json_search "{_ocaml_escape(name)}" {limit}')[0])


@mcp.tool()
def set_goal(goal: str) -> str:
    """Set a new proof goal and return the initial goal state as JSON.

    Args:
        goal: HOL Light term to prove (e.g., "`!n. n + 0 = n`")

    Returns JSON goal state.
    """
    code = (f'ignore(g({goal})); '
            f'print_string (mcp_json_goalstate ()); print_newline ()')
    return _extract_json(_eval_code(code)[0])


@mcp.tool()
def hol_type(term: str) -> str:
    """Get the type of a HOL Light term.

    Args:
        term: Term to get type of (e.g., "`x + y`")

    Returns the type as a string.
    """
    return _strip_ansi(_eval_code(f"type_of {term}")[0])


@mcp.tool()
def hol_load(file: str) -> str:
    """Load a HOL Light file using 'needs'.

    Args:
        file: File path to load (e.g., "Library/words.ml")

    Returns JSON:
        {"success": bool, "file": str, "time_seconds": float}
        On failure: {"success": false, "file": str, "error": str, "time_seconds": float}
    """
    import json as _json
    raw, elapsed = _eval_code(f'needs "{_ocaml_escape(file)}"')
    raw = _strip_ansi(raw)
    if _is_error_output(raw):
        return _json.dumps({
            "success": False, "file": file, "error": raw.strip(),
            "time_seconds": elapsed,
        })
    return _json.dumps({
        "success": True, "file": file, "time_seconds": elapsed,
    })


@mcp.tool()
def hol_interrupt() -> str:
    """Send an interrupt signal to cancel a long-running HOL Light command.

    Use when a tactic hangs (e.g., MESON_TAC on a hard goal).
    After interrupting, the goal state is preserved and you can try
    a different tactic.
    """
    import signal
    with _lock:
        if _proc and _proc.poll() is None:
            _proc.send_signal(signal.SIGINT)
            time.sleep(0.5)
            _drain_queue()
            _reader_buf.clear()
            return "Interrupt sent."
    return "No HOL Light process running."


def _reload_config():
    """Reload the config file selected when the server started."""
    if CONFIG_PATH is None:
        return _effective_config({}, None)
    if not os.path.isfile(CONFIG_PATH):
        raise ValueError(f"Config file no longer exists: {CONFIG_PATH}")
    import tomllib
    try:
        with open(CONFIG_PATH, "rb") as config_file:
            config = tomllib.load(config_file)
    except (OSError, tomllib.TOMLDecodeError) as exc:
        raise ValueError(f"Unable to load config {CONFIG_PATH}: {exc}") from exc
    return _effective_config(config, CONFIG_PATH)


def _config_changes(previous, current):
    changes = {}
    previous = _config_snapshot(previous)
    current = _config_snapshot(current)
    for key in previous:
        if previous[key] != current[key]:
            changes[key] = {"old": previous[key], "new": current[key]}
    return changes


def _apply_runtime_config(config):
    global _config, _runtime_config, TIMEOUT, MAX_OUTPUT_CHARS
    global CONFIGURED_CHECKPOINT, _auto_record_dir
    _config = config["raw"]
    _runtime_config = config
    TIMEOUT = config["timeout"]
    MAX_OUTPUT_CHARS = config["max_output_chars"]
    CONFIGURED_CHECKPOINT = config["checkpoint"]
    _auto_record_dir = config["recording_dir"]


def _process_alive():
    return _proc is not None and _proc.poll() is None


def _terminate_hol():
    global _proc
    proc = _proc
    if proc is None:
        return
    try:
        if proc.poll() is None:
            proc.kill()
        proc.wait(timeout=5)
    except Exception:
        pass
    _proc = None


def _prepare_process_restart():
    global _helpers_loaded, _recording_flushed
    _helpers_loaded = False
    _recording_flushed = len(_recording)
    _drain_queue()
    _reader_buf.clear()


def _quarantine_hol(error):
    """Stop stale HOL state after a forced rebuild failure."""
    global _restart_required, _restart_error, _startup_mode
    global _checkpoint_active, _checkpoint_error, _checkpoint_fingerprint
    _terminate_hol()
    _prepare_process_restart()
    _restart_required = True
    _restart_error = str(error)
    _startup_mode = None
    _checkpoint_active = False
    _checkpoint_error = str(error)
    _checkpoint_fingerprint = None


def _clear_restart_requirement():
    global _restart_required, _restart_error
    _restart_required = False
    _restart_error = None


def _restart_process(checkpoint):
    """Replace the process, falling back to a usable cold HOL on restore errors."""
    global _proc
    _terminate_hol()
    _prepare_process_restart()

    restore_error = None
    try:
        _start_hol(checkpoint, allow_restart_required=True)
        _load_helpers()
    except Exception as exc:
        if _checkpoint_active:
            restore_error = f"Checkpoint restore failed: {exc}"
        else:
            return False, str(exc)

    if restore_error is None and _startup_mode == "cold" and _checkpoint_error:
        return False, _checkpoint_error

    if restore_error is None:
        return True, None

    _terminate_hol()
    _prepare_process_restart()
    try:
        _start_hol(
            checkpoint,
            force_cold=True,
            checkpoint_error=restore_error,
            allow_restart_required=True,
        )
        _load_helpers()
    except Exception as exc:
        return False, f"{restore_error}; cold start also failed: {exc}"
    return False, restore_error


def _run_restart_command(command, stage):
    try:
        result = subprocess.run(
            command,
            cwd=HOL_DIR,
            env=_opam_env(),
            capture_output=True,
            text=True,
        )
    except OSError as exc:
        raise RuntimeError(f"{stage} could not start: {exc}") from exc
    if result.returncode != 0:
        output = "\n".join(
            part.strip() for part in (result.stdout, result.stderr) if part.strip()
        )
        if len(output) > 4000:
            output = output[-4000:]
        raise RuntimeError(
            f"{stage} failed with exit code {result.returncode}"
            + (f":\n{output}" if output else "")
        )


def _build_checkpoint(checkpoint, recipe):
    stage_dir = tempfile.mkdtemp(
        prefix=f".hol-{checkpoint}.ckpt.", dir=HOL_DIR
    )
    shutil.rmtree(stage_dir)
    command = [
        sys.executable,
        os.path.join(MCP_DIR, "make_checkpoint.py"),
        "--name",
        checkpoint,
        "--output-dir",
        stage_dir,
    ]
    for include_dir in recipe["include_dirs"]:
        command.extend(["-I", include_dir])
    command.extend(recipe["loads"])
    try:
        _run_restart_command(command, "checkpoint creation")
        if not _checkpoint_files_in_dir(stage_dir):
            raise RuntimeError(
                f"Checkpoint creation produced no usable files in {stage_dir}"
            )
        return stage_dir
    except Exception:
        if os.path.exists(stage_dir):
            shutil.rmtree(stage_dir, ignore_errors=True)
        raise


def _checkpoint_files_in_dir(path):
    if not os.path.isdir(path):
        return []
    return sorted(
        os.path.join(path, filename)
        for filename in os.listdir(path)
        if filename.startswith("ckpt_") and filename.endswith(".dmtcp")
    )


def _install_checkpoint(checkpoint, staged_dir):
    """Move a staged checkpoint into place, replacing any existing one.

    On failure the caller quarantines HOL and requires a fresh rebuild, so we
    do not attempt to preserve or roll back to the previous checkpoint.
    """
    final_dir = _checkpoint_dir(checkpoint)
    try:
        if os.path.exists(final_dir):
            shutil.rmtree(final_dir)
        os.replace(staged_dir, final_dir)
    except Exception as install_exc:
        return False, f"Unable to install rebuilt checkpoint: {install_exc}"

    if not _checkpoint_files(checkpoint):
        return False, "Installed checkpoint contains no usable files"
    return True, None


def _restart_response(
    started, previous_pid, checkpoint, checkpoint_overridden,
    rebuild_hol_and_checkpoint, changes
):
    return {
        "success": False,
        "rebuild_hol_and_checkpoint": rebuild_hol_and_checkpoint,
        "rebuilt": False,
        "config_reloaded": False,
        "checkpoint": checkpoint,
        "configured_checkpoint": CONFIGURED_CHECKPOINT,
        "checkpoint_overridden": checkpoint_overridden,
        "previous_pid": previous_pid,
        "pid": _proc.pid if _process_alive() else None,
        "startup_mode": _startup_mode,
        "elapsed_seconds": round(time.monotonic() - started, 3),
        "config_changes": changes,
    }


def _hol_restart_sync(checkpoint, rebuild_hol_and_checkpoint, progress):
    started = time.monotonic()
    previous_pid = _proc.pid if _process_alive() else None
    old_process_alive = _process_alive()
    selected = checkpoint or CONFIGURED_CHECKPOINT
    checkpoint_overridden = checkpoint is not None
    changes = {}

    with _restart_lock:
        progress("config_validation", "Reloading and validating configuration")
        try:
            new_config = _reload_config()
            selected = _validate_checkpoint_name(
                checkpoint if checkpoint is not None else new_config["checkpoint"]
            )
            changes = _config_changes(_runtime_config, new_config)
            if _restart_required and not rebuild_hol_and_checkpoint:
                raise ValueError(
                    "A previous HOL/checkpoint rebuild failed. Fix the build "
                    "and run hol_restart(rebuild_hol_and_checkpoint=true) "
                    "before continuing."
                )
            if new_config["recording_dir"] != _auto_record_dir:
                raise ValueError(
                    "recording_dir cannot be changed by hol_restart; "
                    "the existing HOL process and recording were preserved"
                )
            recipe = new_config["checkpoint_recipes"].get(selected)
            if rebuild_hol_and_checkpoint and recipe is None:
                if selected == "base":
                    # "base" is canonically vanilla HOL Light, so it can be
                    # rebuilt without an explicit recipe. Any other checkpoint
                    # must define one; we never rebuild a custom checkpoint as
                    # bare HOL and silently swap it in.
                    recipe = {"include_dirs": [], "loads": []}
                else:
                    raise ValueError(
                        "rebuild_hol_and_checkpoint=True requires "
                        f"checkpoint_recipes.{selected} (only the \"base\" "
                        "checkpoint can be rebuilt without an explicit recipe)"
                    )
            if rebuild_hol_and_checkpoint:
                missing = [
                    path for path in recipe["include_dirs"]
                    if not os.path.isdir(path)
                ]
                if missing:
                    raise ValueError(
                        "Checkpoint recipe include directories do not exist: "
                        + ", ".join(missing)
                    )
        except Exception as exc:
            response = _restart_response(
                started, previous_pid, selected, checkpoint_overridden,
                rebuild_hol_and_checkpoint, changes
            )
            response.update({
                "stage": "config_validation",
                "error": str(exc),
                "hol_preserved": old_process_alive and _process_alive(),
            })
            response["elapsed_seconds"] = round(time.monotonic() - started, 3)
            return response

        _apply_runtime_config(new_config)
        staged_dir = None
        if rebuild_hol_and_checkpoint:
            failure_stage = "clean"
            try:
                progress("clean", "Running make clean")
                _run_restart_command(["make", "clean"], "make clean")
                failure_stage = "build"
                progress("build", "Building HOL Light")
                _run_restart_command(["make"], "make")
                failure_stage = "checkpoint_creation"
                progress(
                    "checkpoint_creation",
                    f"Creating checkpoint {selected}",
                )
                staged_dir = _build_checkpoint(selected, recipe)
            except Exception as exc:
                with _lock:
                    _quarantine_hol(exc)
                response = _restart_response(
                    started, previous_pid, selected, checkpoint_overridden,
                    rebuild_hol_and_checkpoint, changes
                )
                response.update({
                    "config_reloaded": True,
                    "stage": failure_stage,
                    "error": str(exc),
                    "hol_preserved": False,
                })
                response["pid"] = None
                response["startup_mode"] = None
                response["elapsed_seconds"] = round(time.monotonic() - started, 3)
                return response

        progress("restart", f"Restarting HOL with checkpoint {selected}")
        with _lock:
            if rebuild_hol_and_checkpoint:
                installed, install_error = _install_checkpoint(
                    selected, staged_dir
                )
                if not installed:
                    if staged_dir and os.path.exists(staged_dir):
                        shutil.rmtree(staged_dir, ignore_errors=True)
                    _quarantine_hol(install_error)
                    response = _restart_response(
                        started, previous_pid, selected, checkpoint_overridden,
                        rebuild_hol_and_checkpoint, changes
                    )
                    response.update({
                        "config_reloaded": True,
                        "stage": "checkpoint_install",
                        "error": install_error,
                        "hol_preserved": False,
                    })
                    response["pid"] = None
                    response["startup_mode"] = None
                    response["elapsed_seconds"] = round(
                        time.monotonic() - started, 3
                    )
                    return response

                _clear_restart_requirement()
            success, restart_error = _restart_process(selected)

        response = _restart_response(
            started, previous_pid, selected, checkpoint_overridden,
            rebuild_hol_and_checkpoint, changes
        )
        response.update({
            "success": success,
            "rebuilt": rebuild_hol_and_checkpoint,
            "config_reloaded": True,
            "hol_preserved": False,
        })
        if not success:
            response.update({
                "stage": "restart",
                "error": restart_error or "HOL Light restart failed",
            })
        response["pid"] = _proc.pid if _process_alive() else None
        response["startup_mode"] = _startup_mode
        response["elapsed_seconds"] = round(time.monotonic() - started, 3)
        return response


@mcp.tool()
async def hol_restart(
    checkpoint: str | None = None,
    rebuild_hol_and_checkpoint: bool = False,
    ctx: Context = None,
) -> str:
    """Reload configuration and restart the HOL Light subprocess.

    Args:
        checkpoint: Optional checkpoint override for this restart only.
        rebuild_hol_and_checkpoint: Run make clean and make to rebuild HOL
            Light from source, then rebuild the selected checkpoint, before
            restarting. This is a heavy, multi-minute operation, so it must be
            requested explicitly.

    Rebuilding HOL Light and its checkpoint commonly takes several minutes. The
    existing HOL process remains alive until the build and checkpoint creation
    have succeeded.
    """
    events = queue.SimpleQueue()
    executor = ThreadPoolExecutor(
        max_workers=1, thread_name_prefix="hol-restart"
    )
    future = executor.submit(
        _hol_restart_sync,
        checkpoint,
        rebuild_hol_and_checkpoint,
        lambda stage, message: events.put((stage, message)),
    )
    current_stage = None
    stage_started = time.monotonic()
    last_heartbeat = stage_started
    progress_numbers = {
        "config_validation": 1,
        "clean": 2,
        "build": 3,
        "checkpoint_creation": 4,
        "restart": 5,
    }

    try:
        while not future.done():
            while True:
                try:
                    stage, message = events.get_nowait()
                except queue.Empty:
                    break
                current_stage = stage
                stage_started = time.monotonic()
                last_heartbeat = stage_started
                if ctx is not None:
                    await ctx.report_progress(
                        progress_numbers[stage], 5, message
                    )
            now = time.monotonic()
            if (
                ctx is not None
                and current_stage is not None
                and now - last_heartbeat >= RESTART_HEARTBEAT_SECONDS
            ):
                elapsed = round(now - stage_started)
                await ctx.report_progress(
                    progress_numbers[current_stage],
                    5,
                    f"{current_stage.replace('_', ' ')}: {elapsed}s elapsed",
                )
                last_heartbeat = now
            await asyncio.sleep(0.25)

        result = future.result()
    finally:
        executor.shutdown(wait=future.done())
    while True:
        try:
            stage, message = events.get_nowait()
        except queue.Empty:
            break
        if ctx is not None:
            await ctx.report_progress(progress_numbers[stage], 5, message)
    return json.dumps(result)


@mcp.tool()
def hol_status() -> str:
    """Check whether the HOL Light subprocess is alive.

    Returns JSON with process health, active and configured checkpoints,
    startup mode, checkpoint fingerprint/staleness, and runtime limits.
    """
    alive = _proc is not None and _proc.poll() is None
    current_fingerprint = _fingerprint_checkpoint(CHECKPOINT_NAME)
    checkpoint_stale = (
        _checkpoint_fingerprint is not None
        and current_fingerprint != _checkpoint_fingerprint
    )
    return json.dumps({
        "alive": alive,
        "pid": _proc.pid if alive else None,
        "checkpoint": CHECKPOINT_NAME,
        "configured_checkpoint": CONFIGURED_CHECKPOINT,
        "config": CONFIG_PATH,
        "uptime_seconds": round(time.time() - _start_time, 1) if alive and _start_time else None,
        "timeout": TIMEOUT,
        "max_output_chars": MAX_OUTPUT_CHARS,
        "startup_mode": _startup_mode,
        "checkpoint_active": _checkpoint_active,
        "checkpoint_error": _checkpoint_error,
        "checkpoint_fingerprint": _checkpoint_fingerprint,
        "checkpoint_stale": checkpoint_stale,
        "restart_required": _restart_required,
        "restart_error": _restart_error,
    })


@mcp.tool()
def hol_help() -> str:
    """Return the HOL Light tactic reference and proof guide (SKILL.md).

    Call this before your first proof to learn available tactics,
    proof patterns, and common pitfalls.
    """
    return _read_skill()


def _ocaml_escape(s: str) -> str:
    return s.replace("\\", "\\\\").replace('"', '\\"')


def _json_quote(s: str) -> str:
    return '"' + s.replace("\\", "\\\\").replace('"', '\\"').replace("\n", "\\n") + '"'


# --- Proof recording helpers ---

def _flush_recording():
    """Append new entries to the recording file.
    Only writes entries added since the last flush (tracked by _recording_flushed).
    Backtrack writes a marker so replay can skip undone tactics.
    """
    import json
    if not _recording_path:
        return
    with open(_recording_path, 'a') as f:
        global _recording_flushed
        for entry in _recording[_recording_flushed:]:
            f.write(json.dumps(entry) + "\n")
        _recording_flushed = len(_recording)


_recording_flushed = 0  # index of first unflushed entry


def _record_tactic(tactic_str, result_json_str):
    """Record a successful tactic application."""
    import json
    if not _recording_path:
        return
    try:
        result = json.loads(result_json_str)
    except (json.JSONDecodeError, TypeError):
        return
    if "error" in result:
        return
    total = 0 if result.get("proved") else result.get("total_goals", 0)
    _recording.append({"action": "tactic", "tactic": tactic_str, "total_goals": total})
    _flush_recording()


def _record_backtrack(steps):
    """Record a backtrack marker and remove entries from in-memory list."""
    global _recording_flushed
    if not _recording_path:
        return
    removed = 0
    while removed < steps and _recording:
        if _recording[-1]["action"] == "tactic":
            _recording.pop()
            if _recording_flushed > len(_recording):
                _recording_flushed = len(_recording)
            removed += 1
        else:
            break
    if removed > 0:
        _recording.append({"action": "backtrack", "steps": removed})
    _flush_recording()


def _record_tactics_batch(tactics, result_json_str):
    """Record successful tactics from an apply_tactics batch."""
    import json
    if not _recording_path:
        return
    try:
        result = json.loads(result_json_str)
    except (json.JSONDecodeError, TypeError):
        return
    if "error" in result and "step" in result:
        # step = number of tactics that succeeded before the error
        succeeded = result["step"]
    elif "steps" in result:
        succeeded = result["steps"]
    else:
        return
    for i, tac in enumerate(tactics[:succeeded]):
        if i == succeeded - 1:
            total = 0 if result.get("proved") else result.get("total_goals", 0)
        else:
            total = 0
        _recording.append({"action": "tactic", "tactic": tac, "total_goals": total})
    if succeeded > 0:
        _flush_recording()


def _extract_e_tactic(code: str) -> str | None:
    """Extract tactic string from 'e(TACTIC);;' pattern using paren counting."""
    stripped = code.strip()
    m = re.match(r'\s*e\s*\(', stripped)
    if not m:
        return None
    start = m.end()
    depth = 1
    in_str = False
    in_backtick = False
    in_comment = 0
    esc = False
    i = start
    while i < len(stripped):
        c = stripped[i]
        if esc:
            esc = False
            i += 1
            continue
        if in_comment > 0:
            if c == '(' and i + 1 < len(stripped) and stripped[i + 1] == '*':
                in_comment += 1
                i += 2
            elif c == '*' and i + 1 < len(stripped) and stripped[i + 1] == ')':
                in_comment -= 1
                i += 2
            else:
                i += 1
            continue
        if c == '\\' and in_str:
            esc = True
            i += 1
            continue
        if c == '"' and not in_backtick:
            in_str = not in_str
            i += 1
            continue
        if c == '`' and not in_str:
            in_backtick = not in_backtick
            i += 1
            continue
        if in_str or in_backtick:
            i += 1
            continue
        if c == '(' and i + 1 < len(stripped) and stripped[i + 1] == '*':
            in_comment = 1
            i += 2
            continue
        if c == '(':
            depth += 1
        elif c == ')':
            depth -= 1
            if depth == 0:
                return stripped[start:i].strip()
        i += 1
    return None


def _is_backtrack(code: str) -> bool:
    """Check if code is a b() call."""
    stripped = code.strip().rstrip(';').strip()
    return bool(re.match(r'^b\s*\(\s*\)\s*$', stripped))


def _extract_json(output: str) -> str:
    """Extract JSON from print_string output. The output contains the JSON
    printed to stdout, followed by 'val it : unit = ()'."""
    stripped = _strip_ansi(output).strip()
    if stripped.startswith("# "):
        stripped = stripped[2:]
    # Find the earliest JSON start
    obj_idx = stripped.find('{')
    arr_idx = stripped.find('[')
    candidates = []
    if obj_idx != -1:
        candidates.append((obj_idx, '{', '}'))
    if arr_idx != -1:
        candidates.append((arr_idx, '[', ']'))
    if not candidates:
        return '{"error":' + _json_quote(f"Unexpected output: {stripped[:200]}") + '}'
    candidates.sort()
    idx, start_char, end_char = candidates[0]
    depth, in_str, esc = 0, False, False
    for i in range(idx, len(stripped)):
        c = stripped[i]
        if esc:
            esc = False
        elif c == '\\':
            esc = in_str
        elif c == '"':
            in_str = not in_str
        elif not in_str:
            if c == start_char:
                depth += 1
            elif c == end_char:
                depth -= 1
                if depth == 0:
                    return stripped[idx:i+1]
    return '{"error":' + _json_quote(f"Unexpected output: {stripped[:200]}") + '}'


@mcp.tool()
def start_recording(path: str) -> str:
    """Start recording proof tactics to a JSONL file.

    Args:
        path: File path for the recording (e.g., "/tmp/recording.jsonl")

    Returns confirmation message.
    """
    global _recording_path, _recording
    with _lock:
        os.makedirs(os.path.dirname(path) or ".", exist_ok=True)
        _recording_path = path
        _recording = []
        global _recording_flushed
        _recording_flushed = 0
        open(path, 'w').close()  # truncate any existing file
    return f"Recording started: {path}"


@mcp.tool()
def stop_recording() -> str:
    """Stop recording proof tactics and return the recording path.

    Returns the path to the recording file.
    """
    global _recording_path
    with _lock:
        path = _recording_path
        _recording_path = None
    if path:
        return f"Recording stopped: {path}"
    return "No recording was active."


def main():
    _start_hol()
    mcp.run(transport="stdio")


if __name__ == "__main__":
    main()
