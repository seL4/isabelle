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
  'a program = "{(states :: 'a set,
		  init   :: 'a set,
		  acts   :: ('a * 'a)set set).
		 init <= states &
		 acts <= Pow(states Times states) &
		 diag states : acts}"

constdefs
  restrict_rel :: "['a set, ('a * 'a) set] => ('a * 'a) set"
    "restrict_rel A r == (A Times A) Int r"

  mk_program :: "('a set * 'a set * ('a * 'a)set set) => 'a program"
    "mk_program ==
       %(states, init, acts).
	Abs_Program (states,
		     states Int init,
		     restrict_rel states `` (insert Id acts))"

  States :: "'a program => 'a set"
    "States F == (%(states, init, acts). states) (Rep_Program F)"

  Init :: "'a program => 'a set"
    "Init F == (%(states, init, acts). init) (Rep_Program F)"

  Acts :: "'a program => ('a * 'a)set set"
    "Acts F == (%(states, init, acts). acts) (Rep_Program F)"


consts reachable :: "'a program => 'a set"

inductive "reachable F"
  intrs 
    Init  "s: Init F ==> s : reachable F"

    Acts  "[| act: Acts F;  s : reachable F;  (s,s'): act |]
	   ==> s' : reachable F"

end
