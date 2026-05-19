#!/usr/bin/env python3
"""Create a DMTCP checkpoint of HOL Light.

Each extra positional argument must be a single OCaml expression
(e.g. 'needs "foo.ml"').  Expressions are wrapped in try/with to
detect exceptions; multi-phrase inputs containing ';;' are not
supported — place them in a file and load with needs or loadt.

Examples:
    python3 mcp/make_checkpoint.py                          # base HOL Light
    python3 mcp/make_checkpoint.py --name s2n \\
        -I /path/to/s2n-bignum 'needs "arm/proofs/base.ml"'
"""
import argparse
import glob
import os
import shutil
import socket
import subprocess
import sys
import time

HOL_DIR = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
SENTINEL = "HOL_MCP_CKPT_READY"
ERROR_SENTINEL = "HOL_MCP_LOAD_ERROR"


def fatal(msg):
    print(f"ERROR: {msg}", file=sys.stderr, flush=True)
    sys.exit(1)


def parse_args():
    p = argparse.ArgumentParser(
        description="Create a DMTCP checkpoint of HOL Light.",
        epilog="Extra positional arguments are single OCaml expressions evaluated "
               "after HOL Light loads (e.g., 'needs \"arm/proofs/base.ml\"').  "
               "Each expression is wrapped in try/with to detect exceptions.  "
               "Multi-phrase inputs containing ';;' are not supported; place "
               "them in a file and load with needs or loadt.",
    )
    p.add_argument("--name", default="base",
                   help="Checkpoint name (creates hol-<name>.ckpt/). Default: base")
    p.add_argument("-I", dest="include_dirs", action="append", default=[],
                   help="Add OCaml include directory (can be repeated)")
    p.add_argument("extra_loads", nargs="*", metavar="EXPR",
                   help="OCaml expressions to evaluate before checkpointing")
    return p.parse_args()


def build_env():
    """Build environment with opam switch and LD_LIBRARY_PATH."""
    env = os.environ.copy()
    ld_path = os.path.expanduser("~/.local/lib")
    if os.path.isdir(ld_path):
        env["LD_LIBRARY_PATH"] = ld_path + ":" + env.get("LD_LIBRARY_PATH", "")
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


def wait_for_line(proc, marker, error_msg, error_marker=None):
    """Read stdout until a line contains marker. Dies on EOF.

    If error_marker is set, treat any line containing it as a fatal
    error from the OCaml toplevel."""
    while True:
        line = proc.stdout.readline()
        if not line:
            fatal(error_msg)
        if error_marker and error_marker in line:
            # Extract the exception description after the sentinel
            detail = line.strip()
            idx = detail.find(error_marker)
            if idx >= 0:
                detail = detail[idx + len(error_marker):].lstrip(":").strip()
            fatal(f"OCaml exception: {detail}")
        if marker in line:
            return


def send_and_wait(proc, code, error_msg):
    """Send OCaml code wrapped in try/with and wait for sentinel.

    The OCaml toplevel recovers from exceptions and continues to the
    next phrase, so a bare sentinel would appear even after a failure.
    Wrapping in try/with catches the exception and emits an error
    sentinel that wait_for_line detects.

    Only single toplevel expressions are supported.  Multi-phrase
    inputs containing ';;' will be rejected with a helpful message."""
    clean = code.rstrip().rstrip(";")
    if ";;" in clean:
        fatal(
            f"Expression contains ';;' (multiple toplevel phrases):\n"
            f"  {code}\n"
            f"Only single expressions can be error-checked.  Place composite\n"
            f"inputs in a file and use: needs \"file.ml\""
        )
    proc.stdin.write(
        f'(try ({clean}) with e -> '
        f'Printf.printf "{ERROR_SENTINEL}:%s\\n%!" '
        f'(Printexc.to_string e));;\n'
        f'Printf.printf "{SENTINEL}\\n%!";;\n'
    )
    proc.stdin.flush()
    wait_for_line(proc, SENTINEL, error_msg, error_marker=ERROR_SENTINEL)


def main():
    args = parse_args()
    ckpt_dir = os.path.join(HOL_DIR, f"hol-{args.name}.ckpt")
    ocaml_hol = os.path.join(HOL_DIR, "ocaml-hol")

    # Validate prerequisites
    if not os.path.isfile(ocaml_hol):
        fatal(f"ocaml-hol not found at {ocaml_hol}\n  Run: make switch && eval $(opam env) && make")
    if not shutil.which("dmtcp_launch"):
        fatal("dmtcp_launch not found on PATH\n  See mcp/README.md for install instructions")
    for d in args.include_dirs:
        if not os.path.isdir(d):
            fatal(f"Include directory not found: {d}")

    # Clean and recreate checkpoint dir
    if os.path.exists(ckpt_dir):
        shutil.rmtree(ckpt_dir)
    os.makedirs(ckpt_dir)

    # Find a free port for DMTCP coordinator
    s = socket.socket()
    s.bind(("", 0))
    port = s.getsockname()[1]
    s.close()
    os.environ["DMTCP_COORD_PORT"] = str(port)

    env = build_env()

    # Build command
    cmd = [
        "dmtcp_launch", "--new-coordinator", "--ckptdir", ckpt_dir,
        ocaml_hol, "-init", os.path.join(HOL_DIR, "hol.ml"), "-I", HOL_DIR,
    ]
    for d in args.include_dirs:
        cmd.extend(["-I", d])

    if args.include_dirs:
        existing = env.get("HOLLIGHT_LOAD_PATH", "")
        extra = ":".join(args.include_dirs)
        env["HOLLIGHT_LOAD_PATH"] = f"{extra}:{existing}" if existing else extra

    # Print plan
    print(f"Checkpoint: hol-{args.name}.ckpt/", flush=True)
    if args.include_dirs:
        print(f"Include dirs: {args.include_dirs}", flush=True)
    if args.extra_loads:
        print(f"Extra loads: {args.extra_loads}", flush=True)

    # Launch HOL Light under DMTCP
    p = subprocess.Popen(
        cmd, stdin=subprocess.PIPE, stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
        text=True, bufsize=1, cwd=HOL_DIR, env=env,
    )

    print("Waiting for HOL Light to load (~75s)...", flush=True)
    wait_for_line(p, "Camlp5", "HOL Light died before loading. Check that 'make' succeeded.")
    print("HOL Light loaded.", flush=True)

    for expr in args.extra_loads:
        print(f"Loading: {expr}", flush=True)
        send_and_wait(p, expr, f"HOL Light died while loading: {expr}")
        print("  done.", flush=True)

    print("Compacting GC...", flush=True)
    send_and_wait(p, "Gc.compact ()", "HOL Light died during Gc.compact")
    print("  done.", flush=True)

    time.sleep(2)

    print("Checkpointing...", flush=True)
    r = subprocess.run(
        ["dmtcp_command", "--port", str(port), "-bc"],
        capture_output=True, text=True, env=env,
    )
    if r.returncode != 0:
        fatal(f"dmtcp_command failed (rc={r.returncode}): {r.stderr.strip()}")

    # Wait for checkpoint file to appear
    for _ in range(10):
        files = glob.glob(os.path.join(ckpt_dir, "ckpt_*.dmtcp"))
        if files:
            break
        time.sleep(1)
    else:
        fatal("No checkpoint files created")

    subprocess.run(
        ["dmtcp_command", "--port", str(port), "-k"],
        capture_output=True, text=True, env=env,
    )

    size_mb = sum(os.path.getsize(f) for f in files) / (1024 * 1024)
    print(f"Done. {ckpt_dir}/ ({size_mb:.0f}MB)", flush=True)


if __name__ == "__main__":
    main()
