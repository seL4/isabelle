(*  Title:      HOL/UNITY/PPROD.thy
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1998  University of Cambridge

General products of programs (Pi operation), for replicating components.
*)

PPROD = Union + Comp +

constdefs

  (**possible to force all acts to be included in common initial state
      (by intersection) ??*)

  lift_act :: "['a, ('b*'b) set] => (('a=>'b) * ('a=>'b)) set"
    "lift_act i act == {(f,f'). EX s'. f' = f(i:=s') & (f i, s') : act}"

  drop_act :: "['a, (('a=>'b) * ('a=>'b)) set] => ('b*'b) set"
    "drop_act i act == (%(f,f'). (f i, f' i)) `` act"

  lift_set :: "['a, 'b set] => ('a => 'b) set"
    "lift_set i A == {f. f i : A}"

  lift_prog :: "['a, 'b program] => ('a => 'b) program"
    "lift_prog i F ==
       mk_program (lift_set i (Init F),
		   lift_act i `` Acts F)"

  (*products of programs*)
  PPROD  :: ['a set, 'a => 'b program] => ('a => 'b) program
    "PPROD I F == JN i:I. lift_prog i (F i)"

syntax
  "@PPROD" :: [pttrn, 'a set, 'b set] => ('a => 'b) set ("(3PPI _:_./ _)" 10)

translations
  "PPI x:A. B"   == "PPROD A (%x. B)"

end
