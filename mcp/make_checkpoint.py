#!/usr/bin/env python3
"""Create a DMTCP checkpoint of HOL Light with piped stdin."""
import subprocess, time, os, socket, sys, glob

HOL_DIR = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
CKPT_DIR = os.path.join(HOL_DIR, "hol-noledit.ckpt")

# Clean and recreate
subprocess.run(['rm', '-rf', CKPT_DIR])
os.makedirs(CKPT_DIR)

s = socket.socket(); s.bind(('',0)); port = s.getsockname()[1]; s.close()
os.environ['DMTCP_COORD_PORT'] = str(port)
print(f"DMTCP port: {port}", flush=True)

env = os.environ.copy()
# Get opam env
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

p = subprocess.Popen(
    ['dmtcp_launch', '--new-coordinator', '--ckptdir', CKPT_DIR,
     os.path.join(HOL_DIR, 'ocaml-hol'), '-init',
     os.path.join(HOL_DIR, 'hol.ml'), '-I', HOL_DIR],
    stdin=subprocess.PIPE, stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
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

time.sleep(2)

print("Checkpointing...", flush=True)
r = subprocess.run(['dmtcp_command', '--port', str(port), '-bc'],
                    capture_output=True, text=True, env=env)
print(f"  stdout: {r.stdout.strip()!r}", flush=True)
print(f"  stderr: {r.stderr.strip()!r}", flush=True)
print(f"  rc: {r.returncode}", flush=True)

# Wait for checkpoint file
for _ in range(10):
    files = glob.glob(os.path.join(CKPT_DIR, 'ckpt_*.dmtcp'))
    if files:
        break
    time.sleep(1)

files = glob.glob(os.path.join(CKPT_DIR, 'ckpt_*.dmtcp'))
print(f"Checkpoint files: {files}", flush=True)

if not files:
    print("ERROR: No checkpoint files created", flush=True)
    sys.exit(1)

print("Killing coordinator...", flush=True)
subprocess.run(['dmtcp_command', '--port', str(port), '-k'],
               capture_output=True, text=True, env=env)
print(f"Done. Checkpoint in {CKPT_DIR}", flush=True)
