(*  Title:      HOL/UNITY/Constrains
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1998  University of Cambridge

Safety relations: restricted to the set of reachable states.
*)

Constrains = UNITY + Traces + 

constdefs

  Constrains :: "['a program, 'a set, 'a set] => bool"
    "Constrains F A B == 
		 constrains (Acts F)
                            (reachable F  Int  A)
  		            (reachable F  Int  B)"

  Stable     :: "'a program => 'a set => bool"
    "Stable F A == Constrains F A A"

  Unless :: "['a program, 'a set, 'a set] => bool"
    "Unless F A B == Constrains F (A-B) (A Un B)"

  Invariant :: "['a program, 'a set] => bool"
  "Invariant F A == (Init F) <= A & Stable F A"

end
