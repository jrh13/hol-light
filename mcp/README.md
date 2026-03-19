# HOL Light MCP Server

MCP server for the [HOL Light](https://github.com/jrh13/hol-light) theorem prover, designed for LLM-assisted proof search.

## Quick Start

After setup (below), here's a complete proof session:

```
set_goal  "`!n. EVEN n ==> EVEN(n * n)`"
→ {"goals":[{"hypotheses":[],"conclusion":"forall n. EVEN n ==> EVEN (n * n)"}], ...}

apply_tactic  "GEN_TAC THEN STRIP_TAC"
→ {"goals":[{"hypotheses":[{"label":"","term":"EVEN n"}],"conclusion":"EVEN (n * n)"}], ...}

search_theorems  name="EVEN_MULT"
→ [{"name":"EVEN_MULT","statement":"|- forall m n. EVEN (m * n) <=> EVEN m \\/ EVEN n"}]

apply_tactic  "ASM_REWRITE_TAC[EVEN_MULT]"
→ {"proved":true,"theorem":"|- forall n. EVEN n ==> EVEN (n * n)"}
```

See [TUTORIAL.md](TUTORIAL.md) for more examples and [SKILL.md](SKILL.md) for a tactic reference.

## Tools

| Tool | Description | Output |
|------|-------------|--------|
| `eval` | Evaluate arbitrary OCaml/HOL Light code | Raw text (ANSI stripped) |
| `set_goal` | Set a proof goal, return initial state | Structured JSON |
| `goal_state` | Return current proof goals | Structured JSON |
| `apply_tactic` | Apply a tactic, return new state or proved theorem | Structured JSON |
| `backtrack` | Undo tactic steps | Structured JSON |
| `search_theorems` | Search theorem database by name | Structured JSON |
| `hol_type` | Get the type of a term | Raw text |
| `hol_load` | Load a HOL Light file via `needs` | Raw text |

## Setup

```bash
cd mcp && uv sync
```

Requires HOL Light built in the parent directory (`make switch && eval $(opam env) && make`).

## Checkpointing (optional, recommended)

HOL Light takes ~75s to cold start. DMTCP checkpointing reduces this to ~2s.

Requires DMTCP installed (`dmtcp_launch` and `dmtcp_restart` on PATH). To build from source:

```bash
git clone https://github.com/dmtcp/dmtcp.git /tmp/dmtcp
cd /tmp/dmtcp && ./configure --prefix=$HOME/.local && make -j$(nproc) && make install
```

Create a checkpoint:

```bash
export LD_LIBRARY_PATH="$HOME/.local/lib:$LD_LIBRARY_PATH"
python3 mcp/make_checkpoint.py
```

This creates `hol-noledit.ckpt/` in the HOL Light root. The server auto-detects it on startup.

## Usage

```bash
uv run hol-light-mcp
```

The server speaks MCP over stdio.

## Client Configuration

### Kiro CLI (`~/.kiro/settings/mcp.json`)

```json
{
  "mcpServers": {
    "hol-light": {
      "command": "uv",
      "args": ["run", "--directory", "/path/to/hol-light/mcp", "hol-light-mcp"],
      "env": {
        "PATH": "/home/user/.local/bin:/usr/bin:/bin"
      }
    }
  }
}
```

## Tests

```bash
uv run pytest test_server.py -v       # unit tests
uv run python smoke_test.py           # MCP integration test (14 checks)
```

~75s on first run, ~2s with checkpoint.

## Related Work

[mkannwischer/mcp-hol-light](https://github.com/mkannwischer/mcp-hol-light) is another MCP server for HOL Light. It connects to a separate [hol-server](https://github.com/monadius/hol_server) TCP process and exposes a similar set of tools (`hol_eval`, `hol_tactic`, `hol_back`, `hol_search`, etc.). It implements the MCP protocol directly rather than using an SDK, and returns raw REPL text from all tools.

We take a different approach: we embed HOL Light as a subprocess (no external server needed), use OCaml-side JSON serialization to return structured goal states and search results, and support DMTCP checkpointing for instant startup. We find that structured output is particularly useful for automated proof search, where an LLM agent needs to programmatically inspect goals, detect proof completion, and implement backtracking strategies without parsing REPL text.
