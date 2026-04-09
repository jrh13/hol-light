#!/usr/bin/env python3
"""MCP server for HOL Light theorem prover."""

import os
import queue
import re
import subprocess
import sys
import threading
import time

HOL_DIR = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
MCP_DIR = os.path.dirname(os.path.abspath(__file__))
SENTINEL = "HOL_MCP_DONE_a7f3b2e1"
ANSI_RE = re.compile(r"\x1b\[[0-9;]*m")


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
TIMEOUT = _config.get("timeout", int(os.environ.get("HOL_TIMEOUT", "600")))
CHECKPOINT_NAME = _config.get("checkpoint", os.environ.get("HOL_CHECKPOINT", "noledit"))
MAX_OUTPUT_CHARS = _config.get("max_output_chars", int(os.environ.get("HOL_MAX_OUTPUT", "4000")))

from mcp.server.fastmcp import FastMCP
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
_helpers_loaded = False
_start_time = None

# Proof recording state
_recording_path = None  # path to JSONL file; None = not recording
_recording = []         # list of {"action": "tactic", "tactic": ..., "total_goals": ...}

# Queue-based sentinel signaling: reader thread produces results, eval consumes.
# Eliminates race conditions — queue.get() is atomic consumption.
_result_queue = queue.Queue(maxsize=1)
_reader_buf = []


def _reader_thread(proc):
    while True:
        line = proc.stdout.readline()
        if not line:
            # Process died — signal immediately so callers don't hang
            _result_queue.put("[HOL Light process died unexpectedly]")
            break
        if SENTINEL in line:
            _result_queue.put("".join(_reader_buf).strip())
            _reader_buf.clear()
        else:
            _reader_buf.append(line)


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


def _start_hol():
    global _proc
    if _proc is not None:
        return
    ckpt_dir = os.path.join(HOL_DIR, f"hol-{CHECKPOINT_NAME}.ckpt")
    ckpt_files = sorted(
        f for f in os.listdir(ckpt_dir) if f.startswith("ckpt_") and f.endswith(".dmtcp")
    ) if os.path.isdir(ckpt_dir) else []
    if ckpt_files:
        _proc = subprocess.Popen(
            ["dmtcp_restart", "--no-strict-checking", "--coord-port", "0"] +
            [os.path.join(ckpt_dir, f) for f in ckpt_files],
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
    global _start_time
    _start_time = time.time()
    t = threading.Thread(target=_reader_thread, args=(_proc,), daemon=True)
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


@mcp.tool()
def hol_restart() -> str:
    """Kill and restart the HOL Light subprocess.

    Use when HOL Light has died or is in a bad state.
    Any in-progress proof state will be lost.
    """
    global _proc, _helpers_loaded
    with _lock:
        if _proc is not None:
            try:
                _proc.kill()
                _proc.wait(timeout=5)
            except Exception:
                pass
            _proc = None
        _helpers_loaded = False
        _drain_queue()
        _reader_buf.clear()
        _start_hol()
        _load_helpers()
    return "HOL Light restarted."


@mcp.tool()
def hol_status() -> str:
    """Check whether the HOL Light subprocess is alive.

    Returns JSON: {"alive": bool, "pid": int|null, "checkpoint": str,
                   "config": str|null, "uptime_seconds": float|null,
                   "timeout": int, "max_output_chars": int}
    """
    import json
    alive = _proc is not None and _proc.poll() is None
    return json.dumps({
        "alive": alive,
        "pid": _proc.pid if alive else None,
        "checkpoint": CHECKPOINT_NAME,
        "config": CONFIG_PATH,
        "uptime_seconds": round(time.time() - _start_time, 1) if alive and _start_time else None,
        "timeout": TIMEOUT,
        "max_output_chars": MAX_OUTPUT_CHARS,
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
    """Write the current recording to disk.
    Rewrites the full file each time so backtrack deletions are reflected.
    """
    import json
    if _recording_path:
        with open(_recording_path, 'w') as f:
            for entry in _recording:
                f.write(json.dumps(entry) + "\n")


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
    """Remove the last N tactic entries from the recording."""
    if not _recording_path:
        return
    removed = 0
    while removed < steps and _recording:
        if _recording[-1]["action"] == "tactic":
            _recording.pop()
            removed += 1
        else:
            break
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
        # Error at step N: record tactics 0..N-1 (0-indexed, step is 1-indexed)
        succeeded = result["step"] - 1
    elif "steps" in result:
        succeeded = result["steps"]
    else:
        return
    for tac in tactics[:succeeded]:
        _recording.append({"action": "tactic", "tactic": tac, "total_goals": 0})
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
    esc = False
    for i in range(start, len(stripped)):
        c = stripped[i]
        if esc:
            esc = False
            continue
        if c == '\\' and in_str:
            esc = True
            continue
        if c == '"' and not in_backtick:
            in_str = not in_str
            continue
        if c == '`' and not in_str:
            in_backtick = not in_backtick
            continue
        if in_str or in_backtick:
            continue
        if c == '(':
            depth += 1
        elif c == ')':
            depth -= 1
            if depth == 0:
                return stripped[start:i].strip()
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
        _flush_recording()
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
