(*  Title:      Pure/ML-Systems/polyml-4.2.0.ML
    ID:         $Id$
    Author:     Makarius

Compatibility wrapper for Poly/ML 4.9.1.
*)

use "ML-Systems/polyml-4.1.4-patch.ML";
use "ML-Systems/polyml.ML";

val pointer_eq = PolyML.pointerEq;

(* FIXME slow version -- performance test *)
structure String =
struct
  open String;

  fun compare (s1: string, s2) =
    if s1 = s2 then General.EQUAL
    else if s1 < s2 then General.LESS
    else General.GREATER;
end;
