(*  Title:      Pure/ML-Systems/polyml-4.2.0.ML

Compatibility wrapper for Poly/ML 4.2.0.
*)

use "ML-Systems/universal.ML";
use "ML-Systems/thread_dummy.ML";
use "ML-Systems/polyml_common.ML";
use "ML-Systems/polyml_old_compiler4.ML";
use "ML-Systems/polyml_pp.ML";

val pointer_eq = Address.wordEq;

