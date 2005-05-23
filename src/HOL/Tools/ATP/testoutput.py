#!/usr/bin/python

import string
import sys

f = open ("/tmp/args", "w")
for x in sys.argv:
  f.write("%s " % x)
f.write("\n")
f.close()

#f = open ("/home/clq20/scratch/13354/dfg/spassprooflist", "r")
#f = open ("/home/clq20/testoutput.py", "r")

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

for i in range(0, 50):
  print "blah gibberish nonsense"

print """Here is a proof with depth 1, length 9 :
2[0:Inp] || v_P(tconst_fun(typ__Ha,tconst_bool),v_x)* -> v_P(tconst_fun(typ__Ha,tconst_bool),U)*.
3[0:Inp] || v_P(tconst_fun(typ__Ha,tconst_bool),U)*+ -> v_P(tconst_fun(typ__Ha,tconst_bool),v_x)*.
4[0:Inp] ||  -> v_P(tconst_fun(typ__Ha,tconst_bool),U)* v_P(tconst_fun(typ__Ha,tconst_bool),v_xa)*.
5[0:Inp] || v_P(tconst_fun(typ__Ha,tconst_bool),v_xb)* v_P(tconst_fun(typ__Ha,tconst_bool),U)* -> .
6[0:Con:4.0] ||  -> v_P(tconst_fun(typ__Ha,tconst_bool),v_xa)*.
7[0:Con:5.1] || v_P(tconst_fun(typ__Ha,tconst_bool),v_xb)* -> .
8[0:Res:6.0,3.0] ||  -> v_P(tconst_fun(typ__Ha,tconst_bool),v_x)*.
9[0:MRR:2.0,8.0] ||  -> v_P(tconst_fun(typ__Ha,tconst_bool),U)*.
10[0:UnC:9.0,7.0] ||  -> .
Formulae used in the proof :

--------------------------SPASS-STOP------------------------------
"""
