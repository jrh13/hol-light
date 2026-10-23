#!/usr/bin/env python3
"""Remove repeated inlinings from a hol.sh inline-load output: `needs` loads a file once, but the inliner
re-inlines a file at every `needs`/`loadt` of it.  Keeps the FIRST inlining of each path.  Tracks the
include stack through the `#<line> "<path>"` directives (`#1` = start of an inlined file, `#k`, k>1 = resume;
`#1` for a file still open is a resume after a needs on its first line)."""
import re, sys
src, dst = sys.argv[1], sys.argv[2]
lines = open(src).read().split('\n')
direct = re.compile(r'^#(\d+) "([^"]*)"$')
stack = []          # open files
done = set()        # files whose inlining is complete (or in progress)
skip_until = None   # stack length to return to before resuming output
out = []
removed = 0
for ln in lines:
    m = direct.match(ln)
    if m:
        n, path = int(m.group(1)), m.group(2)
        if n == 1 and path not in stack:      # (#1 on an open file: a resume)
            if skip_until is None and path in done:
                skip_until = len(stack)       # skip this re-inlining
                removed += 1
            stack.append(path)
            done.add(path)
        else:
            while stack and stack[-1] != path:
                stack.pop()
            if skip_until is not None and len(stack) <= skip_until:
                skip_until = None
                out.append(ln)              # keep the resume directive for line numbering
                continue
    if skip_until is None:
        out.append(ln)
open(dst, 'w').write('\n'.join(out))
print('removed %d repeated inlinings; %d -> %d lines' % (removed, len(lines), len(out)))
