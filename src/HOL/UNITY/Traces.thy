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


constdefs
  reachable :: "'a set * ('a * 'a)set set => 'a set"
  "reachable == %(Init,Acts). {s. EX evs. (s,evs): traces Init Acts}"

  invariant :: "['a set * ('a * 'a)set set, 'a set] => bool"
  "invariant == %(Init,Acts) A. Init <= A & stable Acts A"

end
