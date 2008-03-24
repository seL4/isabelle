(*  Title:      Pure/ML-Systems/polyml-5.1.ML
    ID:         $Id$

Compatibility wrapper for Poly/ML 5.1.
*)

use "ML-Systems/polyml_common.ML";
use "ML-Systems/multithreading_polyml.ML";

val pointer_eq = PolyML.pointerEq;


(* single-threaded profiling *)

local val profile_orig = profile in

fun profile 0 f x = f x
  | profile n f x = NAMED_CRITICAL "profile" (fn () => profile_orig n f x);

end;

