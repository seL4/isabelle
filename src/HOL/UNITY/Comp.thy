(*  Title:      HOL/UNITY/Comp.thy
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1998  University of Cambridge

Composition
From Chandy and Sanders, "Reasoning About Program Composition",
Technical Report 2000-003, University of Florida, 2000.

Revised by Sidi Ehmety on January  2001 

Added: a strong form of the <= relation (component_of) and localize 

*)

Comp = Union +

instance
  program :: (term)ord

defs
  component_def   "F <= H == EX G. F Join G = H"
  strict_component_def   "(F < (H::'a program)) == (F <= H & F ~= H)"


constdefs
  component_of :: "'a program=>'a program=> bool"
                                    (infixl "component'_of" 50)
  "F component_of H == EX G. F ok G & F Join G = H"

  strict_component_of :: "'a program\\<Rightarrow>'a program=> bool"
                                    (infixl "strict'_component'_of" 50)
  "F strict_component_of H == F component_of H & F~=H"
  
  preserves :: "('a=>'b) => 'a program set"
    "preserves v == INT z. stable {s. v s = z}"

  localize  :: "('a=>'b) => 'a program => 'a program"
  "localize v F == mk_program(Init F, Acts F,
			      AllowedActs F Int (UN G:preserves v. Acts G))"

  funPair      :: "['a => 'b, 'a => 'c, 'a] => 'b * 'c"
  "funPair f g == %x. (f x, g x)"
end
