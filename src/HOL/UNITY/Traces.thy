(*  Title:      HOL/UNITY/Traces
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1998  University of Cambridge

Inductive definitions of
  * traces: the possible execution traces
  * reachable: the set of reachable states
*)

Traces = LessThan +

consts traces :: "['a set, ('a * 'a)set set] => ('a * 'a list) set"

  (*Initial states and program => (final state, reversed trace to it)...
    Arguments MUST be curried in an inductive definition*)

inductive "traces Init Acts"  
  intrs 
         (*Initial trace is empty*)
    Init  "s: Init ==> (s,[]) : traces Init Acts"

    Acts  "[| act: Acts;  (s,evs) : traces Init Acts;  (s,s'): act |]
	   ==> (s', s#evs) : traces Init Acts"


typedef (Program)
  'a program = "{(init:: 'a set, acts :: ('a * 'a)set set). Id:acts}"

constdefs
    mk_program :: "('a set * ('a * 'a)set set) => 'a program"
    "mk_program == %(init, acts). Abs_Program (init, insert Id acts)"

  Init :: "'a program => 'a set"
    "Init F == (%(init, acts). init) (Rep_Program F)"

  Acts :: "'a program => ('a * 'a)set set"
    "Acts F == (%(init, acts). acts) (Rep_Program F)"


consts reachable :: "'a program => 'a set"

inductive "reachable F"
  intrs 
    Init  "s: Init F ==> s : reachable F"

    Acts  "[| act: Acts F;  s : reachable F;  (s,s'): act |]
	   ==> s' : reachable F"

end
