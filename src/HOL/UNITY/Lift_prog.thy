(*  Title:      HOL/UNITY/Lift_prog.thy
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1999  University of Cambridge

lift_prog, etc: replication of components
*)

Lift_prog = Project +

constdefs

  lift_map :: "['a, 'b * ('a => 'b)] => ('a => 'b)"
    "lift_map i == %(s,f). f(i := s)"

  lift_set :: "['a, 'b set] => ('a => 'b) set"
    "lift_set i A == {f. f i : A}"

  drop_set :: "['a, ('a=>'b) set] => 'b set"
    "drop_set i A == (%f. f i) `` A"

  lift_act :: "['a, ('b*'b) set] => (('a=>'b) * ('a=>'b)) set"
    "lift_act i act == {(f,f'). f(i:= f' i) = f' & (f i, f' i) : act}"

  (*Argument C allows weak safety laws to be projected*)
  drop_act :: "[('a=>'b) set, 'a, (('a=>'b) * ('a=>'b)) set] => ('b*'b) set"
    "drop_act C i act == {(f i, f' i) | f f'. (f,f'): act & f: C}"

  lift_prog :: "['a, 'b program] => ('a => 'b) program"
    "lift_prog i F ==
       mk_program (lift_set i (Init F),
		   lift_act i `` Acts F)"

  drop_prog :: "[('a=>'b) set, 'a, ('a=>'b) program] => 'b program"
    "drop_prog C i F ==
       mk_program (drop_set i (Init F),
		   drop_act C i `` (Acts F))"

  (*simplifies the expression of specifications*)
  constdefs
    sub :: ['a, 'a=>'b] => 'b
      "sub i f == f i"


end
