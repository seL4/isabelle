(*  Title:      HOL/UNITY/SubstAx
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1998  University of Cambridge

LeadsTo relation: restricted to the set of reachable states.
*)

SubstAx = WFair + Constrains + 

constdefs

   LeadsTo :: "['a program, 'a set, 'a set] => bool"
    "LeadsTo prg A B ==
		 leadsTo (Acts prg)
                         (reachable prg  Int  A)
  		         (reachable prg  Int  B)"
end
