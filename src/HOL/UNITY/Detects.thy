(*  Title:      HOL/UNITY/Detects
    ID:         $Id$
    Author:     Tanja Vos, Cambridge University Computer Laboratory
    Copyright   2000  University of Cambridge

Detects definition (Section 3.8 of Chandy & Misra) using LeadsTo
*)

Detects = WFair + Reach + 


consts
   op_Detects  :: "['a set, 'a set] => 'a program set"  (infixl "Detects" 60)
   op_Equality :: "['a set, 'a set] => 'a set"          (infixl "<==>" 60)
   
defs
  Detects_def "A Detects B == (Always (-A Un B)) Int (B LeadsTo A)"
  Equality_def "A <==> B == (-A Un B) Int (A Un -B)"

end

