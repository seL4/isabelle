(*  Title:      HOL/UNITY/PPROD.thy
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1998  University of Cambridge

General products of programs (Pi operation), for replicating components.
Also merging of state sets.

The idea of Rsh is to represent sharing in the Right part.
If x and y are states then (Rsh x y) updates y to agree with variables shared
with x.  Therefore Rsh x (Rsh x y) = Rsh x y.  The pair (x,y)
is a valid state of the composite program if and only if y = Rsh x y.

Needs Rcopy; try to do by swapping (symmetry argument)
  instead of repeating all Lcopy proofs.
*)

PPROD = Union + Comp +

constdefs

  sharing :: "[['a,'b]=>'b, 'a set] => ('a*'b) set"
    "sharing Rsh A == SIGMA x: A. range (Rsh x)"

  Lcopy_act :: "[['a,'b]=>'b, ('a*'a) set] => (('a*'b) * ('a*'b)) set"
    "Lcopy_act Rsh act == {((x,y),(x',y')). (x,x'): act & Rsh x y = y &
			                    Rsh x' y = y'}"

  fst_act :: "(('a*'b) * ('a*'b)) set => ('a*'a) set"
    "fst_act act == (%((x,y),(x',y')). (x,x')) `` act"

  Lcopy :: "[['a,'b]=>'b, 'a program] => ('a*'b) program"
    "Lcopy Rsh F == mk_program (sharing Rsh (States F),
			        sharing Rsh (Init F),
			        Lcopy_act Rsh `` Acts F)"

  lift_act :: "['a, ('b*'b) set] => (('a=>'b) * ('a=>'b)) set"
    "lift_act i act == {(f,f'). EX s'. f' = f(i:=s') & (f i, s') : act}"

  drop_act :: "['a, (('a=>'b) * ('a=>'b)) set] => ('b*'b) set"
    "drop_act i act == (%(f,f'). (f i, f' i)) `` act"

  lift_set :: "['a, 'b set] => ('a => 'b) set"
    "lift_set i A == {f. f i : A}"

  lift_prog :: "['a, 'b program] => ('a => 'b) program"
    "lift_prog i F ==
       mk_program (lift_set i (States F),
		   lift_set i (Init F),
		   lift_act i `` Acts F)"

  (*products of programs*)
  PPROD  :: ['a set, 'a => 'b program] => ('a => 'b) program
    "PPROD I F == JN i:I. lift_prog i (F i)"

syntax
  "@PPROD" :: [pttrn, 'a set, 'b set] => ('a => 'b) set ("(3PPI _:_./ _)" 10)

translations
  "PPI x:A. B"   == "PPROD A (%x. B)"


locale Share =
  fixes 
    Rsh	:: ['a,'b]=>'b
  assumes
    (*the last update (from the other side) takes precedence*)
    overwrite "Rsh x (Rsh x' y) = Rsh x y"

end
