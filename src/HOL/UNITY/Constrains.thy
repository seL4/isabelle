(*  Title:      HOL/UNITY/Constrains
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1998  University of Cambridge

Safety relations: restricted to the set of reachable states.
*)

Constrains = UNITY + Traces + 

constdefs

  Constrains :: "['a program, 'a set, 'a set] => bool"
    "Constrains prg A B == 
		 constrains (Acts prg)
                            (reachable prg  Int  A)
  		            (reachable prg  Int  B)"

  Stable     :: "'a program => 'a set => bool"
    "Stable prg A == Constrains prg A A"

  Unless :: "['a program, 'a set, 'a set] => bool"
    "Unless prg A B == Constrains prg (A-B) (A Un B)"

  Invariant :: "['a program, 'a set] => bool"
  "Invariant prg A == (Init prg) <= A & Stable prg A"

end
