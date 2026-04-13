"""Integration tests for HOL Light MCP server.

These tests start a real HOL Light process (~75s cold start, ~2s with checkpoint),
shared across all tests via module-scoped fixture.
"""

import json
import os
import pytest
import server


@pytest.fixture(scope="module", autouse=True)
def hol_process():
    """Start HOL Light once for all tests."""
    result, _ = server._eval_code("1 + 1")
    assert "2" in result, f"HOL Light failed to start: {result[:200]}"
    yield
    if server._proc and server._proc.poll() is None:
        server._proc.terminate()


# --- helpers ---

def _eval_output(code: str, **kwargs) -> str:
    """Call eval tool and return the output field from the JSON response."""
    return json.loads(server.eval(code, **kwargs))["output"]


# --- eval ---

def test_arith_rule():
    r = json.loads(server.eval("ARITH_RULE `1 + 1 = 2`"))
    assert r["success"] is True
    assert "|- 1 + 1 = 2" in r["output"]
    assert r["output_truncated"] is False
    assert isinstance(r["time_seconds"], float)
    assert isinstance(r["full_output_chars"], int)


def test_taut():
    r = json.loads(server.eval("TAUT `p /\\ q ==> q /\\ p`"))
    assert r["success"] is True
    assert "|- p /\\ q ==> q /\\ p" in r["output"]


def test_auto_appends_double_semicolon():
    assert "5" in _eval_output("2 + 3")


def test_error_handling():
    r = json.loads(server.eval("this_does_not_exist"))
    assert r["success"] is False
    assert "Unbound" in r["output"] or "Error" in r["output"]


def test_multi_statement():
    assert "43" in _eval_output("let x = 42;;\nx + 1")


def test_search():
    assert "ADD_SYM" in _eval_output('search [name "ADD_SYM"]')


def test_prove():
    output = _eval_output('prove(`!n. 0 + n = n`, GEN_TAC THEN REWRITE_TAC[ADD])')
    assert "val it : thm" in output
    assert "0 + n = n" in output


def test_eval_truncation():
    # Generate large output and verify truncation
    r = json.loads(server.eval('search [name "ADD"]', max_output_chars=100))
    assert r["output_truncated"] is True
    assert r["full_output_chars"] > 100
    assert r["output"].endswith("... [truncated]")
    assert len(r["output"]) <= 200  # 100 + marker


def test_eval_default_truncation():
    # Default limit should be MAX_OUTPUT_CHARS from config
    r = json.loads(server.eval("1 + 1"))
    assert "full_output_chars" in r


# --- structured tools ---

def test_goal_state_empty():
    result = server._eval_json("mcp_json_goalstate ()")[0]
    gs = json.loads(server._extract_json(result))
    assert gs["goals"] == []


def test_set_goal_and_goal_state():
    server._eval_code("g `!n. n + 0 = n`")
    result = server._eval_json("mcp_json_goalstate ()")[0]
    gs = json.loads(server._extract_json(result))
    assert len(gs["goals"]) == 1
    assert "n + 0 = n" in gs["goals"][0]["conclusion"]


def test_apply_tactic_and_prove():
    server._eval_code("g `!n. n + 0 = n`")
    server._eval_code("e(GEN_TAC THEN ARITH_TAC)")
    result = server._eval_json("mcp_json_after_tactic ()")[0]
    parsed = json.loads(server._extract_json(result))
    assert parsed.get("proved") is True
    assert "n + 0 = n" in parsed["theorem"]


def test_backtrack():
    server._eval_code("g `!n. n + 0 = n`")
    server._eval_code("e(GEN_TAC)")
    result = server._eval_json("mcp_json_backtrack 1")[0]
    gs = json.loads(server._extract_json(result))
    assert "n + 0 = n" in gs["goals"][0]["conclusion"]


def test_search_theorems():
    result = server._eval_json('mcp_json_search "ADD_SYM" 5')[0]
    results = json.loads(server._extract_json(result))
    assert len(results) > 0
    assert any("ADD_SYM" in r["name"] for r in results)


# --- hol_status ---

def test_hol_status_alive():
    result = json.loads(server.hol_status())
    assert result["alive"] is True
    assert isinstance(result["pid"], int)
    assert isinstance(result["checkpoint"], str)
    assert result["config"] is None or isinstance(result["config"], str)
    assert result["uptime_seconds"] > 0
    assert isinstance(result["timeout"], int)
    assert isinstance(result["max_output_chars"], int)


def test_hol_status_reports_checkpoint_name():
    result = json.loads(server.hol_status())
    assert result["checkpoint"] == server.CHECKPOINT_NAME


# --- per-call timeout ---

def test_eval_with_custom_timeout():
    r = json.loads(server.eval("1 + 1", timeout=30))
    assert r["success"] is True
    assert "2" in r["output"]


def test_apply_tactic_with_custom_timeout():
    server._eval_code("g `!n. n + 0 = n`")
    result = json.loads(server.apply_tactic("GEN_TAC THEN ARITH_TAC", timeout=30))
    assert result.get("proved") is True


def test_eval_timeout_expires():
    r = json.loads(server.eval("let rec loop () = loop () in loop ()", timeout=1))
    assert r["success"] is False or "timeout" in r["output"].lower()
    server.hol_restart()


# --- hol_restart ---

def test_hol_restart():
    old_pid = server._proc.pid
    result = server.hol_restart()
    assert "restarted" in result.lower()
    assert server._proc.poll() is None
    assert server._proc.pid != old_pid
    r = json.loads(server.eval("1 + 1"))
    assert "2" in r["output"]


# --- prove tool ---

def test_prove_tool_success():
    result = json.loads(server.prove("`!n. 0 + n = n`", "GEN_TAC THEN REWRITE_TAC[ADD]"))
    assert result["proved"] is True
    assert "0 + n = n" in result["theorem"]


def test_prove_tool_error():
    result = json.loads(server.prove("`!n. 0 + n = n`", "REWRITE_TAC[]"))
    assert "error" in result


# --- apply_tactics tool ---

def test_apply_tactics_completes_proof():
    server._eval_code("g `!n. n + 0 = n`")
    result = json.loads(server.apply_tactics(["GEN_TAC", "ARITH_TAC"]))
    assert result["proved"] is True
    assert "n + 0 = n" in result["theorem"]
    assert result["steps"] == 2


def test_apply_tactics_partial():
    server._eval_code("g `!m n. m + n = n + m`")
    result = json.loads(server.apply_tactics(["GEN_TAC", "GEN_TAC"]))
    assert "goals" in result
    assert result["steps"] == 2


def test_apply_tactics_error_stops():
    server._eval_code("g `T /\\ T`")
    result = json.loads(server.apply_tactics(["CONJ_TAC", "CONJ_TAC"]))
    assert "error" in result
    assert result["step"] == 1


def test_apply_tactics_empty():
    result = json.loads(server.apply_tactics([]))
    assert "error" in result


# --- goal_state tool ---

def test_goal_state_tool_empty():
    server._eval_code("g `T`")
    server._eval_code("e(REWRITE_TAC[])")
    result = json.loads(server.goal_state())
    assert "goals" in result
    assert "total_goals" in result


def test_goal_state_tool_with_goal():
    server.set_goal("`T /\\ T`")
    result = json.loads(server.goal_state())
    assert len(result["goals"]) >= 1


# --- set_goal tool ---

def test_set_goal_tool():
    result = json.loads(server.set_goal("`!n. n + 0 = n`"))
    assert len(result["goals"]) == 1
    assert "n + 0 = n" in result["goals"][0]["conclusion"]


# --- backtrack tool ---

def test_backtrack_tool():
    server.set_goal("`!n. n + 0 = n`")
    server.apply_tactic("GEN_TAC")
    result = json.loads(server.backtrack())
    assert "n + 0 = n" in result["goals"][0]["conclusion"]
    assert "n" in result["goals"][0]["conclusion"]


# --- search_theorems tool ---

def test_search_theorems_tool():
    results = json.loads(server.search_theorems("ADD_SYM", limit=5))
    assert len(results) > 0
    assert any("ADD_SYM" in r["name"] for r in results)


def test_search_theorems_tool_limit():
    results = json.loads(server.search_theorems("ADD", limit=3))
    assert len(results) <= 3


# --- hol_type tool ---

def test_hol_type_tool():
    result = server.hol_type("`1 + 1`")
    assert "num" in result


def test_hol_type_tool_bool():
    result = server.hol_type("`T`")
    assert "bool" in result


# --- hol_load tool ---

def test_hol_load_tool():
    result = json.loads(server.hol_load("Library/iter.ml"))
    assert result["success"] is True
    assert result["file"] == "Library/iter.ml"
    assert isinstance(result["time_seconds"], float)


def test_hol_load_tool_error():
    result = json.loads(server.hol_load("nonexistent_file_12345.ml"))
    assert result["success"] is False
    assert "error" in result
    assert result["file"] == "nonexistent_file_12345.ml"


# --- hol_interrupt tool ---

def test_hol_interrupt_no_hang():
    result = server.hol_interrupt()
    assert "Interrupt sent" in result or "No HOL Light process" in result


# --- hol_help tool ---

def test_hol_help_tool():
    result = server.hol_help()
    assert "## Core tactics" in result
    assert "prove" in result.lower()


# --- start_recording / stop_recording tools ---

def test_start_recording(tmp_path):
    path = str(tmp_path / "rec.jsonl")
    result = server.start_recording(path)
    assert "Recording started" in result
    assert os.path.exists(path)
    server.stop_recording()


def test_stop_recording_returns_path(tmp_path):
    path = str(tmp_path / "rec.jsonl")
    server.start_recording(path)
    result = server.stop_recording()
    assert path in result


def test_stop_recording_when_inactive():
    result = server.stop_recording()
    assert "No recording" in result


def test_recording_captures_apply_tactic(tmp_path):
    path = str(tmp_path / "rec.jsonl")
    server.start_recording(path)
    server.set_goal("`!n. n + 0 = n`")
    server.apply_tactic("GEN_TAC THEN ARITH_TAC")
    server.stop_recording()
    with open(path) as f:
        entries = [json.loads(line) for line in f if line.strip()]
    assert len(entries) == 1
    assert entries[0]["action"] == "tactic"
    assert entries[0]["tactic"] == "GEN_TAC THEN ARITH_TAC"


def test_recording_backtrack_removes_entry(tmp_path):
    path = str(tmp_path / "rec.jsonl")
    server.start_recording(path)
    server.set_goal("`!n. n + 0 = n`")
    server.apply_tactic("GEN_TAC")
    server.backtrack()
    server.stop_recording()
    with open(path) as f:
        entries = [json.loads(line) for line in f if line.strip()]
    assert len(entries) == 0


def test_recording_skips_failed_tactic(tmp_path):
    path = str(tmp_path / "rec.jsonl")
    server.start_recording(path)
    server.set_goal("`T`")
    server.apply_tactic("FAKE_NONEXISTENT_TAC")
    server.stop_recording()
    with open(path) as f:
        entries = [json.loads(line) for line in f if line.strip()]
    assert len(entries) == 0


def test_start_recording_creates_parent_dirs(tmp_path):
    path = str(tmp_path / "nested" / "dir" / "rec.jsonl")
    server.start_recording(path)
    assert os.path.exists(path)
    server.stop_recording()


def test_recording_captures_apply_tactics_batch(tmp_path):
    path = str(tmp_path / "rec.jsonl")
    server.start_recording(path)
    server.set_goal("`!n. n + 0 = n`")
    server.apply_tactics(["GEN_TAC", "ARITH_TAC"])
    server.stop_recording()
    with open(path) as f:
        entries = [json.loads(line) for line in f if line.strip()]
    assert len(entries) == 2
    assert entries[0]["tactic"] == "GEN_TAC"
    assert entries[1]["tactic"] == "ARITH_TAC"


def test_recording_captures_eval_e_tactic(tmp_path):
    path = str(tmp_path / "rec.jsonl")
    server.start_recording(path)
    server.set_goal("`!n. n + 0 = n`")
    server.eval("e(GEN_TAC);;")
    server.stop_recording()
    with open(path) as f:
        entries = [json.loads(line) for line in f if line.strip()]
    assert len(entries) == 1
    assert entries[0]["tactic"] == "GEN_TAC"


def test_recording_backtrack_removes_last(tmp_path):
    path = str(tmp_path / "rec.jsonl")
    server.start_recording(path)
    server.set_goal("`!m n. m + n = n + m`")
    server.apply_tactic("GEN_TAC")
    server.apply_tactic("GEN_TAC")
    server.backtrack()
    server.stop_recording()
    with open(path) as f:
        entries = [json.loads(line) for line in f if line.strip()]
    assert len(entries) == 1
    assert entries[0]["tactic"] == "GEN_TAC"
