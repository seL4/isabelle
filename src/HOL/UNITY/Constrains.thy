(*  Title:      HOL/UNITY/Constrains
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1998  University of Cambridge

Safety relations: restricted to the set of reachable states.
*)

Constrains = UNITY + 

consts traces :: "['a set, ('a * 'a)set set] => ('a * 'a list) set"

  (*Initial states and program => (final state, reversed trace to it)...
    Arguments MUST be curried in an inductive definition*)

inductive "traces init acts"  
  intrs 
         (*Initial trace is empty*)
    Init  "s: init ==> (s,[]) : traces init acts"

    Acts  "[| act: acts;  (s,evs) : traces init acts;  (s,s'): act |]
	   ==> (s', s#evs) : traces init acts"


consts reachable :: "'a program => 'a set"

inductive "reachable F"
  intrs 
    Init  "s: Init F ==> s : reachable F"

    Acts  "[| act: Acts F;  s : reachable F;  (s,s'): act |]
	   ==> s' : reachable F"

constdefs

  Constrains :: "['a set, 'a set] => 'a program set"
    "Constrains A B == {F. F : constrains (reachable F  Int  A)
  		                          (reachable F  Int  B)}"

  Stable     :: "'a set => 'a program set"
    "Stable A == Constrains A A"

  Unless :: "['a set, 'a set] => 'a program set"
    "Unless A B == Constrains (A-B) (A Un B)"

  Invariant :: "'a set => 'a program set"
    "Invariant A == {F. Init F <= A} Int Stable A"

  (*Polymorphic in both states and the meaning of <= *)
  Increasing :: "['a => 'b::{ord}] => 'a program set"
    "Increasing f == INT z. Stable {s. z <= f s}"

end
