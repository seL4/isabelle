(*  Title:      ZF/UNITY/Comp.thy
    ID:         $Id$
    Author:     Sidi O Ehmety, Computer Laboratory
    Copyright   1998  University of Cambridge

Composition
From Chandy and Sanders, "Reasoning About Program Composition",
Technical Report 2000-003, University of Florida, 2000.

Revised by Sidi Ehmety on January  2001 

Added: a strong form of the order relation over component and localize 

Theory ported from HOL.
  
*)

Comp = Union +

constdefs

  component :: [i, i] => o  (infixl 65) 
  "F component H == (EX G. F Join G = H)"

  strict_component :: [i, i] => o (infixl "strict'_component" 65)
  "F strict_component H == F component H & F~=H"

  (* A stronger form of the component relation *)
  component_of :: "[i,i]=>o"   (infixl "component'_of" 65)
  "F component_of H  == (EX G. F ok G & F Join G = H)"
  
  strict_component_of :: "[i,i]=>o" (infixl "strict'_component'_of" 65)
  "F strict_component_of H  == F component_of H  & F~=H"

  (* Preserves a state function f, in particular a variable *)
  preserves :: (i=>i)=>i
  "preserves(f) == {F:program. ALL z. F: stable({s:state. f(s) = z})}"

localize  :: "[i=>i, i] => i"
  "localize(f,F) == mk_program(Init(F), Acts(F),
			       AllowedActs(F) Int (UN G:preserves(f). Acts(G)))"

  
  end
