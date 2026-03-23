#!/usr/bin/env python3
"""Create a DMTCP checkpoint of HOL Light with piped stdin.

Usage:
    python3 make_checkpoint.py                                              # bare HOL Light
    python3 make_checkpoint.py --name base                                  # named checkpoint
    python3 make_checkpoint.py --name s2n -I /path/to/s2n-bignum 'needs "arm/proofs/base.ml"'
"""
import subprocess, time, os, socket, sys, glob

HOL_DIR = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
SENTINEL = "HOL_MCP_CKPT_READY"

# Parse args
include_dirs = []
extra_loads = []
ckpt_name = "noledit"
i = 1
while i < len(sys.argv):
    if sys.argv[i] == "-I" and i + 1 < len(sys.argv):
        include_dirs.append(sys.argv[i + 1])
        i += 2
    elif sys.argv[i] == "--name" and i + 1 < len(sys.argv):
        ckpt_name = sys.argv[i + 1]
        i += 2
    else:
        extra_loads.append(sys.argv[i])
        i += 1

CKPT_DIR = os.path.join(HOL_DIR, f"hol-{ckpt_name}.ckpt")

# Clean and recreate
subprocess.run(['rm', '-rf', CKPT_DIR])
os.makedirs(CKPT_DIR)

s = socket.socket(); s.bind(('',0)); port = s.getsockname()[1]; s.close()
os.environ['DMTCP_COORD_PORT'] = str(port)
print(f"DMTCP port: {port}", flush=True)

env = os.environ.copy()
try:
    r = subprocess.run(['opam', 'env', '--switch', HOL_DIR + '/', '--set-switch'],
                       capture_output=True, text=True)
    for line in r.stdout.strip().split('\n'):
        if '=' in line and "'" in line:
            key = line.split('=', 1)[0].strip()
            val = line.split("'")[1]
            env[key] = val
except FileNotFoundError:
    pass

cmd = [
    'dmtcp_launch', '--new-coordinator', '--ckptdir', CKPT_DIR,
    os.path.join(HOL_DIR, 'ocaml-hol'), '-init',
    os.path.join(HOL_DIR, 'hol.ml'), '-I', HOL_DIR,
]
for d in include_dirs:
    cmd.extend(['-I', d])

# Set HOLLIGHT_LOAD_PATH so needs/loadt can find files in include dirs
if include_dirs:
    existing = env.get('HOLLIGHT_LOAD_PATH', '')
    extra = ':'.join(include_dirs)
    env['HOLLIGHT_LOAD_PATH'] = f"{extra}:{existing}" if existing else extra

print(f"HOL_DIR: {HOL_DIR}", flush=True)
if include_dirs:
    print(f"Include dirs: {include_dirs}", flush=True)

p = subprocess.Popen(
    cmd, stdin=subprocess.PIPE, stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
    text=True, bufsize=1, cwd=HOL_DIR, env=env)

print("Waiting for HOL Light to load...", flush=True)
while True:
    line = p.stdout.readline()
    if not line:
        print("ERROR: EOF before HOL Light loaded", flush=True)
        sys.exit(1)
    if 'Camlp5' in line:
        print("HOL Light loaded.", flush=True)
        break

for load_cmd in extra_loads:
    print(f"Loading: {load_cmd}", flush=True)
    p.stdin.write(f'{load_cmd};;\nPrintf.printf "{SENTINEL}\\n%!";;\n')
    p.stdin.flush()
    while True:
        line = p.stdout.readline()
        if not line:
            print("ERROR: EOF during extra loading", flush=True)
            sys.exit(1)
        if SENTINEL in line:
            print(f"  done.", flush=True)
            break

time.sleep(2)

print("Checkpointing...", flush=True)
r = subprocess.run(['dmtcp_command', '--port', str(port), '-bc'],
                    capture_output=True, text=True, env=env)
print(f"  rc: {r.returncode}", flush=True)

for _ in range(10):
    files = glob.glob(os.path.join(CKPT_DIR, 'ckpt_*.dmtcp'))
    if files:
        break
    time.sleep(1)

files = glob.glob(os.path.join(CKPT_DIR, 'ckpt_*.dmtcp'))
if not files:
    print("ERROR: No checkpoint files created", flush=True)
    sys.exit(1)

print("Killing coordinator...", flush=True)
subprocess.run(['dmtcp_command', '--port', str(port), '-k'],
               capture_output=True, text=True, env=env)
print(f"Done. Checkpoint files: {[os.path.basename(f) for f in files]}", flush=True)
