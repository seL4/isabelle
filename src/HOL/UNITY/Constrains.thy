(*  Title:      HOL/UNITY/Constrains
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1998  University of Cambridge

Safety relations: restricted to the set of reachable states.
*)

Constrains = UNITY + Traces + 

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

end
