(*  Title:      ZF/UNITY/SubstAx.thy
    ID:         $Id$
    Author:     Sidi O Ehmety, Computer Laboratory
    Copyright   2001  University of Cambridge

Weak LeadsTo relation (restricted to the set of reachable states)

Theory ported from HOL.
*)

SubstAx = WFair + Constrains + 

constdefs
   Ensures :: "[i,i] => i"            (infixl 60)
    "A Ensures B == {F:program. F : (reachable(F) Int A) ensures B &
		                A:condition & B:condition}"

   LeadsTo :: "[i, i] => i"            (infixl 60)
    "A LeadsTo B == {F:program. F:(reachable(F) Int A) leadsTo B &
		                A:condition & B:condition}"

syntax (xsymbols)
  "op LeadsTo" :: "[i, i] => i" (infixl " \\<longmapsto>w " 60)

end
