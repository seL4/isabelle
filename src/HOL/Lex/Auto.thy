(*  Title: 	HOL/Lex/Auto.thy
    ID:         $Id$
    Author: 	Tobias Nipkow
    Copyright   1995 TUM

Automata expressed as triples of
  1. a start state,
  2. a transition function and
  3. a test for final states.

NOTE: this functional representation is suitable for all kinds of automata,
      not just finite ones!
*)

Auto = Prefix +

types ('a,'b)auto = "'b * ('b => 'a => 'b) * ('b => bool)"

consts
  start :: "('a, 'b)auto => 'b"
  next  :: "('a, 'b)auto => ('b => 'a => 'b)"
  fin   :: "('a, 'b)auto => ('b => bool)"
  nexts :: "('a, 'b)auto => 'b => 'a list => 'b"
  accepts :: "('a,'b) auto => 'a list => bool"  
  acc_prefix :: "('a, 'b)auto => 'b => 'a list => bool"

defs
  start_def "start(A) == fst(A)"
  next_def  "next(A) == fst(snd(A))"
  fin_def   "fin(A) == snd(snd(A))"
  nexts_def "nexts(A) == foldl(next(A))"

  accepts_def "accepts A xs == fin A (nexts A (start A) xs)"

  acc_prefix_def
    "acc_prefix A st xs == ? us. us <= xs & us~=[] & fin A (nexts A st us)"

end
