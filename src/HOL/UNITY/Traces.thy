(*  Title:      HOL/UNITY/Traces
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1998  University of Cambridge

Inductive definitions of
  * traces: the possible execution traces
  * reachable: the set of reachable states
*)

Traces = UNITY +

consts traces :: "['a set, ('a * 'a)set set] => ('a * 'a list) set"

  (*Initial states and program => (final state, reversed trace to it)...
    Arguments MUST be curried in an inductive definition*)

inductive "traces Init Acts"  
  intrs 
         (*Initial trace is empty*)
    Init  "s: Init ==> (s,[]) : traces Init Acts"

    Acts  "[| act: Acts;  (s,evs) : traces Init Acts;  (s,s'): act |]
	   ==> (s', s#evs) : traces Init Acts"


record 'a program =
  Init :: 'a set
  Acts :: "('a * 'a)set set"


consts reachable :: "'a program => 'a set"

inductive "reachable prg"
  intrs 
    Init  "s: Init prg ==> s : reachable prg"

    Acts  "[| act: Acts prg;  s : reachable prg;  (s,s'): act |]
	   ==> s' : reachable prg"

end
