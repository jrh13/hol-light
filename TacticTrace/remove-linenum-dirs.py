"""
Remove line number directives from a source file:
'#<line number> <file name>'
"""

import sys

f = open(sys.argv[1], "r")
ls = list(f.readlines())
f.close()
for i in range(0, len(ls)):
  l = ls[i]
  if not l.startswith("#"):
    continue
  if not (' ' in l):
    continue
  n = l[1:l.index(' ')]
  if n.isdigit():
    ls[i] = "\n"

f = open(sys.argv[2], "w")
for l in ls:
  f.write(l)
f.close()
