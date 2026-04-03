"""Integration tests for HOL Light MCP server.

These tests start a real HOL Light process (~75s cold start, ~2s with checkpoint),
shared across all tests via module-scoped fixture.
"""

import json
import pytest
import server


@pytest.fixture(scope="module", autouse=True)
def hol_process():
    """Start HOL Light once for all tests."""
    result = server._eval_code("1 + 1")
    assert "2" in result, f"HOL Light failed to start: {result[:200]}"
    yield
    if server._proc and server._proc.poll() is None:
        server._proc.terminate()


# --- eval ---

def test_arith_rule():
    result = server._eval_code("ARITH_RULE `1 + 1 = 2`")
    assert "|- 1 + 1 = 2" in result


def test_taut():
    result = server._eval_code("TAUT `p /\\ q ==> q /\\ p`")
    assert "|- p /\\ q ==> q /\\ p" in result


def test_auto_appends_double_semicolon():
    result = server._eval_code("2 + 3")
    assert "5" in result


def test_error_handling():
    result = server._eval_code("this_does_not_exist")
    assert "Error" in result or "Unbound" in result


def test_multi_statement():
    result = server._eval_code("let x = 42;;\nx + 1")
    assert "43" in result


def test_search():
    result = server._eval_code('search [name "ADD_SYM"]')
    assert "ADD_SYM" in result


def test_prove():
    result = server._eval_code(
        'prove(`!n. 0 + n = n`, GEN_TAC THEN REWRITE_TAC[ADD])'
    )
    assert "val it : thm" in result
    assert "0 + n = n" in result


# --- structured tools ---

def test_goal_state_empty():
    result = server._eval_json("mcp_json_goalstate ()")
    gs = json.loads(server._extract_json(result))
    assert gs["goals"] == []


def test_set_goal_and_goal_state():
    server._eval_code("g `!n. n + 0 = n`")
    result = server._eval_json("mcp_json_goalstate ()")
    gs = json.loads(server._extract_json(result))
    assert len(gs["goals"]) == 1
    assert "n + 0 = n" in gs["goals"][0]["conclusion"]


def test_apply_tactic_and_prove():
    server._eval_code("g `!n. n + 0 = n`")
    server._eval_code("e(GEN_TAC THEN ARITH_TAC)")
    result = server._eval_json("mcp_json_after_tactic ()")
    parsed = json.loads(server._extract_json(result))
    assert parsed.get("proved") is True
    assert "n + 0 = n" in parsed["theorem"]


def test_backtrack():
    server._eval_code("g `!n. n + 0 = n`")
    server._eval_code("e(GEN_TAC)")
    result = server._eval_json("mcp_json_backtrack 1")
    gs = json.loads(server._extract_json(result))
    assert "n + 0 = n" in gs["goals"][0]["conclusion"]


def test_search_theorems():
    result = server._eval_json('mcp_json_search "ADD_SYM" 5')
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


def test_hol_status_reports_checkpoint_name():
    result = json.loads(server.hol_status())
    assert result["checkpoint"] == server.CHECKPOINT_NAME


# --- per-call timeout ---

def test_eval_with_custom_timeout():
    result = server.eval("1 + 1", timeout=30)
    assert "2" in result


def test_apply_tactic_with_custom_timeout():
    server._eval_code("g `!n. n + 0 = n`")
    result = json.loads(server.apply_tactic("GEN_TAC THEN ARITH_TAC", timeout=30))
    assert result.get("proved") is True


def test_eval_timeout_expires():
    # Infinite loop should exceed a 1-second timeout
    result = server.eval("let rec loop () = loop () in loop ()", timeout=1)
    assert "timeout" in result.lower()
    # The process is now stuck; restart so subsequent tests work
    server.hol_restart()


# --- hol_restart ---

def test_hol_restart():
    old_pid = server._proc.pid
    result = server.hol_restart()
    assert "restarted" in result.lower()
    assert server._proc.poll() is None, "new process should be alive"
    assert server._proc.pid != old_pid
    # verify it works after restart
    result = server.eval("1 + 1")
    assert "2" in result


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
    # Second tactic should fail — goal after CONJ_TAC has no conjunction
    result = json.loads(server.apply_tactics(["CONJ_TAC", "CONJ_TAC"]))
    assert "error" in result
    assert result["step"] == 1


def test_apply_tactics_empty():
    result = json.loads(server.apply_tactics([]))
    assert "error" in result



# --- goal_state tool ---

def test_goal_state_tool_empty():
    # Complete any leftover proof, then check goal_state returns valid JSON
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
    # After backtrack, the universal quantifier should be restored
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
    # Loading an already-loaded file should succeed (idempotent via needs)
    result = server.hol_load("list.ml")
    # needs returns empty or "already loaded" — just check no error
    assert "Failure" not in result and "Error" not in result


# --- hol_interrupt tool ---

def test_hol_interrupt_no_hang():
    result = server.hol_interrupt()
    # Should return one of the two expected messages
    assert "Interrupt sent" in result or "No HOL Light process" in result


# --- hol_help tool ---

def test_hol_help_tool():
    result = server.hol_help()
    assert "## Core tactics" in result
    assert "prove" in result.lower()

