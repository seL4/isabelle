(*  Title:      HOL/UNITY/SubstAx
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1998  University of Cambridge

LeadsTo relation: restricted to the set of reachable states.
*)

SubstAx = WFair + Constrains + 

constdefs

   LeadsTo :: "['a set, 'a set] => 'a program set"
    "LeadsTo A B == {F. F : leadsTo (reachable F  Int  A)
	   	                    (reachable F  Int  B)}"
end
