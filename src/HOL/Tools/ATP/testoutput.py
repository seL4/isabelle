#!/usr/bin/python

import string
import sys

mode = 0
try:
  while 1:
    line = sys.stdin.readline()
    words = line.split()
    if len(words) > 0:
      if words[0] == "SPASS":
        mode = 1
    if line == '':
      break
    line = line[:-1]
    if mode == 1:
      print line
except:
  pass
#f.close()

sys.exit()

