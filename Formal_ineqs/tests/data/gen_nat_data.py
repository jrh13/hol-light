#!/usr/bin/python

# -*- coding: utf-8 -*-
"""
Created on Tue May 12 12:23:42 2015

@author: alexey
"""

import sys
import random

if len(sys.argv) != 3:
    print "Usage: gen_nat_data length n"
    sys.exit(1)

length = int(sys.argv[1])
n = int(sys.argv[2])

assert (length >= 1 and length <= 1000)
assert (n >= 1 and n <= 10000000)

a = 10 ** length
b = 10 ** (length + 1) - 1

for i in range(0, n):
    print random.randint(a, b)