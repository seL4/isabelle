(*  Title:      HOL/UNITY/PPROD.thy
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1998  University of Cambridge

General products of programs (Pi operation).
Also merging of state sets.
*)

PPROD = Union + Comp +

constdefs
  (*Cartesian product of two relations*)
  RTimes :: "[('a*'a) set, ('b*'b) set] => (('a*'b) * ('a*'b)) set"
	("_ RTimes _" [81, 80] 80)

    "R RTimes S == {((x,y),(x',y')). (x,x'):R & (y,y'):S}"

(*FIXME: syntax (symbols) to use <times> ??
  RTimes :: "[('a*'a) set, ('b*'b) set] => (('a*'b) * ('a*'b)) set"
    ("_ \\<times> _" [81, 80] 80)
*)

constdefs
  fst_act :: "(('a*'b) * ('a*'b)) set => ('a*'a) set"
    "fst_act act == (%((x,y),(x',y')). (x,x')) `` act"

  Lcopy :: "'a program => ('a*'b) program"
    "Lcopy F == mk_program (Init F Times UNIV,
			    (%act. act RTimes Id) `` Acts F)"

  lift_act :: "['a, ('b*'b) set] => (('a=>'b) * ('a=>'b)) set"
    "lift_act i act == {(f,f'). EX s'. f' = f(i:=s') & (f i, s') : act}"

  drop_act :: "['a, (('a=>'b) * ('a=>'b)) set] => ('b*'b) set"
    "drop_act i act == (%(f,f'). (f i, f' i)) `` act"

  lift_prog :: "['a, 'b program] => ('a => 'b) program"
    "lift_prog i F == mk_program ({f. f i : Init F}, lift_act i `` Acts F)"

  (*products of programs*)
  PPROD  :: ['a set, 'a => 'b program] => ('a => 'b) program
    "PPROD I F == JN i:I. lift_prog i (F i)"

syntax
  "@PPROD" :: [pttrn, 'a set, 'b set] => ('a => 'b) set ("(3PPI _:_./ _)" 10)

translations
  "PPI x:A. B"   == "PPROD A (%x. B)"

end
