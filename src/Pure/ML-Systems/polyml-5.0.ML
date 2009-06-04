(*  Title:      Pure/ML-Systems/polyml-5.0.ML

Compatibility wrapper for Poly/ML 5.0.
*)

fun reraise exn = raise exn;

use "ML-Systems/universal.ML";
use "ML-Systems/thread_dummy.ML";
use "ML-Systems/ml_name_space.ML";
use "ML-Systems/polyml_common.ML";
use "ML-Systems/compiler_polyml-5.0.ML";
use "ML-Systems/pp_polyml.ML";

val pointer_eq = PolyML.pointerEq;

fun share_common_data () = PolyML.shareCommonData PolyML.rootFunction;

