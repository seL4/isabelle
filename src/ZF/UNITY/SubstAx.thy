(*  Title:      ZF/UNITY/SubstAx.thy
    ID:         $Id$
    Author:     Sidi O Ehmety, Computer Laboratory
    Copyright   2001  University of Cambridge

Weak LeadsTo relation (restricted to the set of reachable states)

Theory ported from HOL.
*)

SubstAx = WFair + Constrains + 

constdefs
  (* The definitions below are not `conventional', but yields simpler rules *)
   Ensures :: "[i,i] => i"            (infixl 60)
    "A Ensures B == {F:program. F : (reachable(F) Int A) ensures (reachable(F) Int B) }"

  LeadsTo :: "[i, i] => i"            (infixl 60)
    "A LeadsTo B == {F:program. F:(reachable(F) Int A) leadsTo (reachable(F) Int B)}"

syntax (xsymbols)
  "op LeadsTo" :: "[i, i] => i" (infixl " \\<longmapsto>w " 60)

end
