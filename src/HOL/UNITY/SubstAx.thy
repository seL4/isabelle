(*  Title:      HOL/UNITY/SubstAx
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1998  University of Cambridge

My treatment of the Substitution Axiom -- not as an axiom!
*)

SubstAx = WFair +

constdefs

   LeadsTo :: "['a program, 'a set, 'a set] => bool"
    "LeadsTo prg A B ==
		 leadsTo (Acts prg)
                         (reachable prg  Int  A)
  		         (reachable prg  Int  B)"
end
