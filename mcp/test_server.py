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
