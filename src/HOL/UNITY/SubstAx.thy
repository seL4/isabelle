(*  Title:      HOL/UNITY/SubstAx
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1998  University of Cambridge

My treatment of the Substitution Axiom -- not as an axiom!
*)

SubstAx = WFair +

constdefs

   LeadsTo :: "['a set, ('a * 'a)set set, 'a set, 'a set] => bool"
    "LeadsTo Init Acts A B ==
     leadsTo Acts (reachable Init Acts Int A)
                  (reachable Init Acts Int B)"


end
