(*  Title:      HOL/UNITY/SubstAx
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1998  University of Cambridge

Weak LeadsTo relation (restricted to the set of reachable states)
*)

SubstAx = WFair + Constrains + 

constdefs
   LeadsTo :: "['a set, 'a set] => 'a program set"            (infixl 60)
    "A LeadsTo B == {F. F : (reachable F Int A) leadsTo B}"

end
