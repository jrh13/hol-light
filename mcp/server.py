#!/usr/bin/env python3
"""MCP server for HOL Light theorem prover."""

import os
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
            return tomllib.load(f)
    return {}


_config = _load_config()
TIMEOUT = _config.get("timeout", int(os.environ.get("HOL_TIMEOUT", "600")))
CHECKPOINT_NAME = _config.get("checkpoint", os.environ.get("HOL_CHECKPOINT", "noledit"))

from mcp.server.fastmcp import FastMCP
mcp = FastMCP("hol-light")

_proc = None
_lock = threading.Lock()
_output_buf = []
_helpers_loaded = False


def _reader_thread(proc):
    for line in iter(proc.stdout.readline, ""):
        _output_buf.append(line)


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
    t = threading.Thread(target=_reader_thread, args=(_proc,), daemon=True)
    t.start()


def _wait_for_sentinel(timeout=None):
    if timeout is None:
        timeout = TIMEOUT
    deadline = time.time() + timeout
    while time.time() < deadline:
        for i, line in enumerate(_output_buf):
            if SENTINEL in line:
                result = "".join(_output_buf[:i])
                _output_buf[:] = _output_buf[i + 1:]
                return result.strip()
        time.sleep(0.05)
    return "[timeout waiting for HOL Light response]"


def _load_helpers():
    global _helpers_loaded
    if _helpers_loaded:
        return
    helpers_path = os.path.join(MCP_DIR, "mcp_helpers.ml")
    _output_buf.clear()
    cmd = f'#use "{helpers_path}";;\nPrintf.printf "{SENTINEL}\\n%!";;\n'
    _proc.stdin.write(cmd)
    _proc.stdin.flush()
    result = _wait_for_sentinel()
    if "MCP helpers loaded" in result:
        _helpers_loaded = True
    else:
        raise RuntimeError(f"Failed to load MCP helpers: {result}")


def _eval_raw(code: str) -> str:
    """Eval code, return raw output. Caller must hold _lock and ensure HOL is started."""
    _output_buf.clear()
    full = code.rstrip()
    if not full.endswith(";;"):
        full += ";;"
    full += f'\nPrintf.printf "{SENTINEL}\\n%!";;\n'
    _proc.stdin.write(full)
    _proc.stdin.flush()
    return _wait_for_sentinel()


def _eval_code(code: str) -> str:
    with _lock:
        _start_hol()
        _load_helpers()
        return _eval_raw(code)


def _eval_json(code: str) -> str:
    """Eval OCaml code that produces a string, print it to stdout, return it.
    Uses print_string to avoid OCaml's string truncation in REPL output."""
    with _lock:
        _start_hol()
        _load_helpers()
        return _eval_raw(f'print_string ({code}); print_newline ()')


def _strip_ansi(s: str) -> str:
    return ANSI_RE.sub("", s)


@mcp.tool()
def eval(code: str) -> str:
    """Evaluate OCaml/HOL Light code and return the output.

    Examples:
        ARITH_RULE `1 + 1 = 2`;;
        TAUT `p /\\ q ==> q /\\ p`;;
        search [name "ARITH"];;
    """
    return _strip_ansi(_eval_code(code))


@mcp.tool()
def goal_state() -> str:
    """Return the current goal state as JSON.

    Returns JSON: {"goals": [{"hypotheses": [...], "conclusion": "..."}],
                   "num_subgoals": N, "total_goals": M}
    Returns empty goals list if no proof is in progress.
    """
    return _extract_json(_eval_json("mcp_json_goalstate ()"))


@mcp.tool()
def apply_tactic(tactic: str) -> str:
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
    with _lock:
        _start_hol()
        _load_helpers()
        tac_result = _eval_raw(f"e({tactic})")
        if "Exception" in tac_result or "Error" in tac_result or "Failure" in tac_result:
            err = _strip_ansi(tac_result).strip()
            return '{"error":' + _json_quote(err) + '}'
        result = _eval_raw("print_string (mcp_json_after_tactic ()); print_newline ()")
        return _extract_json(result)


@mcp.tool()
def backtrack(steps: int = 1) -> str:
    """Undo tactic steps and return the resulting goal state as JSON.

    Args:
        steps: Number of steps to undo (default 1).

    Returns JSON goal state or {"error": "..."} if can't back up.
    """
    return _extract_json(_eval_json(f"mcp_json_backtrack {steps}"))


@mcp.tool()
def search_theorems(name: str, limit: int = 20) -> str:
    """Search the theorem database by name and return results as JSON.

    Args:
        name: Substring to search for in theorem names.
        limit: Maximum results to return (default 20).

    Returns JSON array: [{"name": "...", "statement": "..."}, ...]
    """
    return _extract_json(_eval_json(f'mcp_json_search "{_ocaml_escape(name)}" {limit}'))


@mcp.tool()
def set_goal(goal: str) -> str:
    """Set a new proof goal and return the initial goal state as JSON.

    Args:
        goal: HOL Light term to prove (e.g., "`!n. n + 0 = n`")

    Returns JSON goal state.
    """
    with _lock:
        _start_hol()
        _load_helpers()
        _eval_raw(f"g({goal})")
        result = _eval_raw("print_string (mcp_json_goalstate ()); print_newline ()")
        return _extract_json(result)


@mcp.tool()
def hol_type(term: str) -> str:
    """Get the type of a HOL Light term.

    Args:
        term: Term to get type of (e.g., "`x + y`")

    Returns the type as a string.
    """
    return _strip_ansi(_eval_code(f"type_of {term}"))


@mcp.tool()
def hol_load(file: str) -> str:
    """Load a HOL Light file using 'needs'.

    Args:
        file: File path to load (e.g., "Library/words.ml")

    Returns the output from loading.
    """
    return _strip_ansi(_eval_code(f'needs "{_ocaml_escape(file)}"'))


@mcp.tool()
def hol_interrupt() -> str:
    """Send an interrupt signal to cancel a long-running HOL Light command.

    Use when a tactic hangs (e.g., MESON_TAC on a hard goal).
    After interrupting, the goal state is preserved and you can try
    a different tactic.
    """
    import signal
    if _proc and _proc.poll() is None:
        _proc.send_signal(signal.SIGINT)
        time.sleep(0.5)
        _output_buf.clear()
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
        _output_buf.clear()
        _start_hol()
        _load_helpers()
    return "HOL Light restarted."


def _ocaml_escape(s: str) -> str:
    return s.replace("\\", "\\\\").replace('"', '\\"')


def _json_quote(s: str) -> str:
    return '"' + s.replace("\\", "\\\\").replace('"', '\\"').replace("\n", "\\n") + '"'


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


def main():
    _start_hol()
    mcp.run(transport="stdio")


if __name__ == "__main__":
    main()
