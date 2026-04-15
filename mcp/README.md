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

Or as a one-shot proof:

```
prove  goal="`!n. EVEN n ==> EVEN(n * n)`"  tactic="GEN_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[EVEN_MULT]"
→ {"proved":true,"theorem":"|- forall n. EVEN n ==> EVEN (n * n)"}
```

See [TUTORIAL.md](TUTORIAL.md) for more examples (including s2n-bignum ARM proofs) and [SKILL.md](SKILL.md) for a tactic reference.

## Tools

| Tool | Description | Output |
|------|-------------|--------|
| `eval` | Evaluate arbitrary OCaml/HOL Light code | Structured JSON (truncated) |
| `set_goal` | Set a proof goal, return initial state | Structured JSON |
| `goal_state` | Return current proof goals | Structured JSON |
| `apply_tactic` | Apply a tactic, return new state or proved theorem | Structured JSON |
| `apply_tactics` | Apply a list of tactics in one round-trip | Structured JSON |
| `prove` | One-shot prove: goal + tactic → theorem | Structured JSON |
| `backtrack` | Undo tactic steps | Structured JSON |
| `search_theorems` | Search theorem database by name | Structured JSON |
| `hol_type` | Get the type of a term | Raw text |
| `hol_load` | Load a HOL Light file via `needs` | Structured JSON |
| `hol_interrupt` | Cancel a long-running command | Status message |
| `hol_restart` | Kill and restart the HOL Light subprocess | Status message |
| `hol_status` | Check process health, uptime, config, checkpoint | Structured JSON |
| `hol_help` | Return tactic reference and proof guide (SKILL.md) | Markdown text |
| `start_recording` | Start recording proof tactics to a JSONL file | Status message |
| `stop_recording` | Stop recording and return the file path | Status message |

`eval` returns `{"success", "output", "output_truncated", "full_output_chars", "time_seconds"}`. Large outputs are truncated to `max_output_chars` (default 4000, configurable). Override per-call with `max_output_chars=N`.

`hol_load` returns `{"success", "file", "time_seconds"}` (plus `"error"` on failure). Intermediate output is suppressed — use `eval` with `needs "file.ml"` if you need verbose output.

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

Create named checkpoints:

```bash
export LD_LIBRARY_PATH="$HOME/.local/lib:$LD_LIBRARY_PATH"

# Bare HOL Light (~75s)
python3 mcp/make_checkpoint.py --name base

# With s2n-bignum ARM infrastructure (~5-10min)
python3 mcp/make_checkpoint.py --name s2n -I /path/to/s2n-bignum 'needs "arm/proofs/base.ml"'
```

## Configuration

By default, the server loads `/path/to/hol-light/mcp/hol-mcp.toml`. To use a different config, pass `--config /absolute/path/to/hol-mcp.toml`.

```toml
# Which checkpoint to use (looks for /path/to/hol-light/hol-<name>.ckpt/).
checkpoint = "s2n"

# Timeout in seconds for HOL Light commands.
timeout = 600

# Maximum characters for eval output before truncation.
max_output_chars = 4000
```

Use `hol_status` to verify which config file and checkpoint are active.

## Usage

```bash
uv run hol-light-mcp
uv run hol-light-mcp --config /path/to/hol-mcp.toml
```

The server speaks MCP over stdio.

## Client Configuration

### Kiro CLI (`~/.kiro/settings/mcp.json`)

```json
{
  "mcpServers": {
    "hol-light": {
      "command": "uv",
      "args": ["run", "--directory", "/path/to/hol-light/mcp", "hol-light-mcp",
               "--config", "/path/to/your/project/hol-mcp.toml"],
      "env": {
        "PATH": "/home/user/.local/bin:/usr/bin:/bin"
      }
    }
  }
}
```

### Skill / Tactic Guide

The server includes a built-in `hol_help` tool that returns the full tactic reference and proof guide ([SKILL.md](SKILL.md)). The LLM can call it before its first proof — no extra configuration needed.

## Tests

```bash
cd mcp
uv run pytest test_server.py -v       # 48 unit tests
uv run python smoke_test.py           # 37 MCP integration checks
```

First run includes HOL Light startup (~75s cold, ~2s with checkpoint).

## Security Considerations

The `eval` tool executes arbitrary OCaml code, which has full access to the host system. This is inherent to theorem proving. However, the server uses stdio transport (no network sockets), so it is only accessible to the MCP client process that spawned it. It is not exposed to the network, even on an EC2 instance with open ports.

Treat DMTCP checkpoint files (`hol-<name>.ckpt/`) as executable code---don't restore untrusted checkpoints.

## Related Work

[mkannwischer/mcp-hol-light](https://github.com/mkannwischer/mcp-hol-light) is another MCP server for HOL Light. It connects to a separate [hol-server](https://github.com/monadius/hol_server) TCP process and exposes a similar set of tools (`hol_eval`, `hol_tactic`, `hol_back`, `hol_search`, etc.). It implements the MCP protocol directly rather than using an SDK, and returns raw REPL text from all tools.

We take a different approach: we embed HOL Light as a subprocess (no external server needed), use OCaml-side JSON serialization to return structured goal states and search results, and support DMTCP checkpointing for instant startup. We find that structured output is particularly useful for automated proof search, where an LLM agent needs to programmatically inspect goals, detect proof completion, and implement backtracking strategies without parsing REPL text.

## Acknowledgments

Thanks to kceren for advice on HOL Light tactics and proof patterns, to nebeid for suggesting named checkpoints, and to the s2n-bignum team for encouragement and tutorial examples.
