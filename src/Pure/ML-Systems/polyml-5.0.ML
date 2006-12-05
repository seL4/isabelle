(*  Title:      Pure/ML-Systems/polyml-5.0.ML
    ID:         $Id$

Compatibility wrapper for Poly/ML 5.0.
*)

use "ML-Systems/polyml-4.1.4-patch.ML";
use "ML-Systems/polyml.ML";

val pointer_eq = PolyML.pointerEq;
