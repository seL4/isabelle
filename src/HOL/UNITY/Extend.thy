(*  Title:      HOL/UNITY/Extend.thy
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1998  University of Cambridge

Extending of state sets
  function f (forget)    maps the extended state to the original state
  function g (forgotten) maps the extended state to the "extending part"
*)

Extend = Union + Comp +

constdefs

  extend_set :: "['a*'b => 'c, 'a set] => 'c set"
    "extend_set h A == h `` (A Times UNIV)"

  extend_act :: "['a*'b => 'c, ('a*'a) set] => ('c * 'c) set"
    "extend_act h == (%act. UN (s,s'): act. UN y. {(h(s,y), h(s',y))})"

  extend :: "['a*'b => 'c, 'a program] => 'c program"
    "extend h F == mk_program (extend_set h (Init F),
			       extend_act h `` Acts F)"

locale Extend =
  fixes 
    f       :: 'c => 'a
    g       :: 'c => 'b
    h       :: "'a*'b => 'c"    (*isomorphism between 'a * 'b and 'c *)
    slice   :: ['c set, 'b] => 'a set
    f_act   :: "('c * 'c) set => ('a*'a) set"

  assumes
    inj_h  "inj h"
    surj_h "surj h"
  defines
    f_def       "f z == fst (inv h z)"
    g_def       "g z == snd (inv h z)"
    slice_def   "slice Z y == {x. h(x,y) : Z}"
    f_act_def   "f_act act == (%(z,z'). (f z, f z')) `` act"

end
