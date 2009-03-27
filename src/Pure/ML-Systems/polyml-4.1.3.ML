(*  Title:      Pure/ML-Systems/polyml-4.1.3.ML

Compatibility wrapper for Poly/ML 4.1.3.
*)

use "ML-Systems/polyml_old_basis.ML";
use "ML-Systems/universal.ML";
use "ML-Systems/thread_dummy.ML";
use "ML-Systems/ml_name_space.ML";
use "ML-Systems/polyml_common.ML";
use "ML-Systems/polyml_old_compiler4.ML";
use "ML-Systems/polyml_pp.ML";

val pointer_eq = Address.wordEq;

