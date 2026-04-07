#!/usr/bin/env python3
"""Smoke test: starts hol-light-mcp as a real MCP server and runs all tools."""

import asyncio
import json
import sys
from mcp.client.stdio import stdio_client, StdioServerParameters
from mcp.client.session import ClientSession

SERVER = StdioServerParameters(
    command="uv",
    args=["run", "--directory", __import__("os").path.dirname(__import__("os").path.abspath(__file__)), "hol-light-mcp"],
)

passed = 0
failed = 0


def check(name, condition, detail=""):
    global passed, failed
    if condition:
        passed += 1
        print(f"  ✓ {name}")
    else:
        failed += 1
        print(f"  ✗ {name}")
        if detail:
            print(f"    {detail[:200]}")


async def main():
    print("Starting hol-light-mcp server...")
    async with stdio_client(SERVER) as (read, write):
        async with ClientSession(read, write) as session:
            await session.initialize()

            # Check tools registered
            tools = await session.list_tools()
            tool_names = sorted(t.name for t in tools.tools)
            check("tools registered", tool_names == ["apply_tactic", "apply_tactics", "backtrack", "eval", "goal_state", "hol_help", "hol_interrupt", "hol_load", "hol_restart", "hol_status", "hol_type", "prove", "search_theorems", "set_goal"],
                  f"got {tool_names}")

            # eval — basic arithmetic (now returns JSON)
            r = await session.call_tool("eval", {"code": "ARITH_RULE `1 + 1 = 2`"})
            ev = json.loads(r.content[0].text)
            check("eval: ARITH_RULE success", ev["success"] is True, str(ev))
            check("eval: ARITH_RULE output", "|- 1 + 1 = 2" in ev["output"], ev["output"])
            check("eval: has time_seconds", isinstance(ev["time_seconds"], float), str(ev))
            check("eval: has full_output_chars", isinstance(ev["full_output_chars"], int), str(ev))

            # eval — truncation
            r = await session.call_tool("eval", {"code": 'search [name "ADD"]', "max_output_chars": 100})
            ev = json.loads(r.content[0].text)
            check("eval: truncation works", ev["output_truncated"] is True and ev["full_output_chars"] > 100, str(ev))

            # goal_state — no goal set
            r = await session.call_tool("goal_state", {})
            gs = json.loads(r.content[0].text)
            check("goal_state: empty", gs["goals"] == [] and gs["total_goals"] == 0, str(gs))

            # Set a goal via set_goal
            r = await session.call_tool("set_goal", {"goal": "`!n. n + 0 = n`"})
            gs = json.loads(r.content[0].text)
            check("set_goal: returns goal", len(gs["goals"]) == 1, str(gs))

            # goal_state — should have one goal
            r = await session.call_tool("goal_state", {})
            gs = json.loads(r.content[0].text)
            check("goal_state: has goal", len(gs["goals"]) == 1, str(gs))
            check("goal_state: conclusion", "n + 0 = n" in gs["goals"][0]["conclusion"], str(gs))

            # apply_tactic — GEN_TAC
            r = await session.call_tool("apply_tactic", {"tactic": "GEN_TAC"})
            gs = json.loads(r.content[0].text)
            check("apply_tactic: GEN_TAC", len(gs["goals"]) >= 1, str(gs))

            # backtrack
            r = await session.call_tool("backtrack", {"steps": 1})
            gs = json.loads(r.content[0].text)
            check("backtrack: restored", "n + 0 = n" in gs["goals"][0]["conclusion"], str(gs))

            # apply_tactic — complete the proof
            r = await session.call_tool("apply_tactic", {"tactic": "GEN_TAC THEN ARITH_TAC"})
            result = json.loads(r.content[0].text)
            check("apply_tactic: proof complete", result.get("proved") == True, str(result))
            check("apply_tactic: theorem", "n + 0 = n" in result.get("theorem", ""), str(result))

            # apply_tactic — error case
            await session.call_tool("eval", {"code": "g `T`"})
            r = await session.call_tool("apply_tactic", {"tactic": "FAKE_NONEXISTENT_TAC"})
            result = json.loads(r.content[0].text)
            check("apply_tactic: error", "error" in result, str(result))

            # search_theorems
            r = await session.call_tool("search_theorems", {"name": "ADD_SYM", "limit": 5})
            results = json.loads(r.content[0].text)
            check("search_theorems: found", len(results) > 0, str(results))
            check("search_theorems: has name", any("ADD_SYM" in entry["name"] for entry in results), str(results))

            # hol_type
            r = await session.call_tool("hol_type", {"term": "`1 + 1`"})
            check("hol_type", "num" in r.content[0].text, r.content[0].text)

            # hol_load (now returns JSON)
            r = await session.call_tool("hol_load", {"file": "list.ml"})
            hl = json.loads(r.content[0].text)
            check("hol_load: success", hl["success"] is True, str(hl))
            check("hol_load: has time", isinstance(hl["time_seconds"], float), str(hl))

            # hol_status
            r = await session.call_tool("hol_status", {})
            status = json.loads(r.content[0].text)
            check("hol_status: alive", status["alive"] is True, str(status))
            check("hol_status: has pid", isinstance(status["pid"], int), str(status))
            check("hol_status: has max_output_chars", isinstance(status["max_output_chars"], int), str(status))

            # hol_help
            r = await session.call_tool("hol_help", {})
            check("hol_help", "## Core tactics" in r.content[0].text, r.content[0].text[:200])

            # hol_interrupt
            r = await session.call_tool("hol_interrupt", {})
            check("hol_interrupt", "Interrupt sent" in r.content[0].text or "No HOL Light process" in r.content[0].text, r.content[0].text)

            # prove tool
            r = await session.call_tool("prove", {"goal": "`!n. 0 + n = n`", "tactic": "GEN_TAC THEN REWRITE_TAC[ADD]"})
            result = json.loads(r.content[0].text)
            check("prove: success", result.get("proved") == True, str(result))
            check("prove: theorem", "0 + n = n" in result.get("theorem", ""), str(result))

            r = await session.call_tool("prove", {"goal": "`!n. 0 + n = n`", "tactic": "REWRITE_TAC[]"})
            result = json.loads(r.content[0].text)
            check("prove: error", "error" in result, str(result))

            # apply_tactics tool
            await session.call_tool("eval", {"code": "g `!n. n + 0 = n`"})
            r = await session.call_tool("apply_tactics", {"tactics": ["GEN_TAC", "ARITH_TAC"]})
            result = json.loads(r.content[0].text)
            check("apply_tactics: proof complete", result.get("proved") == True, str(result))
            check("apply_tactics: steps", result.get("steps") == 2, str(result))

            # eval with per-call timeout
            r = await session.call_tool("eval", {"code": "1 + 1", "timeout": 30})
            ev = json.loads(r.content[0].text)
            check("eval: custom timeout", "2" in ev["output"], ev["output"])

            # hol_restart (run last — kills the process)
            r = await session.call_tool("hol_restart", {})
            check("hol_restart", "restarted" in r.content[0].text.lower(), r.content[0].text)
            r = await session.call_tool("eval", {"code": "1 + 1"})
            ev = json.loads(r.content[0].text)
            check("eval after restart", "2" in ev["output"], ev["output"])

            print(f"\n{passed}/{passed + failed} passed")
            return failed == 0


if __name__ == "__main__":
    success = asyncio.run(main())
    sys.exit(0 if success else 1)
