(*  Title:      Pure/ML-Systems/polyml-4.9.1.ML
    ID:         $Id$

Compatibility wrapper for Poly/ML 4.9.1.
*)

use "ML-Systems/polyml-4.1.4-patch.ML";
use "ML-Systems/polyml.ML";

val pointer_eq = PolyML.pointerEq;
