(*  Title:      HOL/UNITY/Extend.thy
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1998  University of Cambridge

Extending of state sets
  function f (forget)    maps the extended state to the original state
  function g (forgotten) maps the extended state to the "extending part"
*)

Extend = Guar +

constdefs

  (*MOVE to Relation.thy?*)
  Restrict :: "[ 'a set, ('a*'b) set] => ('a*'b) set"
    "Restrict A r == r Int (A <*> UNIV)"

  good_map :: "['a*'b => 'c] => bool"
    "good_map h == surj h & (ALL x y. fst (inv h (h (x,y))) = x)"
     (*Using the locale constant "f", this is  f (h (x,y))) = x*)
  
  extend_set :: "['a*'b => 'c, 'a set] => 'c set"
    "extend_set h A == h `` (A <*> UNIV)"

  project_set :: "['a*'b => 'c, 'c set] => 'a set"
    "project_set h C == {x. EX y. h(x,y) : C}"

  extend_act :: "['a*'b => 'c, ('a*'a) set] => ('c*'c) set"
    "extend_act h == %act. UN (s,s'): act. UN y. {(h(s,y), h(s',y))}"

  project_act :: "['a*'b => 'c, ('c*'c) set] => ('a*'a) set"
    "project_act h act == {(x,x'). EX y y'. (h(x,y), h(x',y')) : act}"

  extend :: "['a*'b => 'c, 'a program] => 'c program"
    "extend h F == mk_program (extend_set h (Init F),
			       extend_act h `` Acts F,
			       project_act h -`` AllowedActs F)"

  (*Argument C allows weak safety laws to be projected*)
  project :: "['a*'b => 'c, 'c set, 'c program] => 'a program"
    "project h C F ==
       mk_program (project_set h (Init F),
		   project_act h `` Restrict C `` Acts F,
		   {act. Restrict (project_set h C) act :
		         project_act h `` Restrict C `` AllowedActs F})"

locale Extend =
  fixes 
    f       :: 'c => 'a
    g       :: 'c => 'b
    h       :: "'a*'b => 'c"    (*isomorphism between 'a * 'b and 'c *)
    slice   :: ['c set, 'b] => 'a set

  assumes
    good_h  "good_map h"
  defines
    f_def       "f z == fst (inv h z)"
    g_def       "g z == snd (inv h z)"
    slice_def   "slice Z y == {x. h(x,y) : Z}"

end
