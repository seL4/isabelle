(*  Title:      HOL/Lex/Auto.thy
    ID:         $Id$
    Author:     Tobias Nipkow
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

constdefs

  start :: ('a, 'b)auto => 'b
  "start(A) == fst(A)"

  next  :: ('a, 'b)auto => ('b => 'a => 'b)
  "next(A) == fst(snd(A))"

  fin   :: ('a, 'b)auto => ('b => bool)
  "fin(A) == snd(snd(A))"

  nexts :: ('a, 'b)auto => 'b => 'a list => 'b
  "nexts(A) == foldl(next(A))"

  accepts :: ('a,'b) auto => 'a list => bool
  "accepts A xs == fin A (nexts A (start A) xs)"

  acc_prefix :: ('a, 'b)auto => 'b => 'a list => bool
  "acc_prefix A st xs == ? us. us <= xs & us~=[] & fin A (nexts A st us)"

end
