(*  Title:      Pure/ML-Systems/polyml-5.1.ML
    ID:         $Id$

Compatibility wrapper for Poly/ML 5.1.
*)

open Thread;
use "ML-Systems/polyml_common.ML";
use "ML-Systems/multithreading_polyml.ML";
use "ML-Systems/polyml_old_compiler5.ML";

val pointer_eq = PolyML.pointerEq;
