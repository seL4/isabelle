(*  Title:      HOL/UNITY/Comp.thy
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1998  University of Cambridge

Composition

From Chandy and Sanders, "Reasoning About Program Composition"
*)

Comp = Union +

instance
  program :: (term)ord

defs

  component_def   "F <= H == EX G. F Join G = H"

  strict_component_def   "(F < (H::'a program)) == (F <= H & F ~= H)"

end
