use "pgip_types.ML";
use "pgip_markup.ML";
use "pgip_input.ML";
use "pgip_output.ML";
use "pgip.ML";
use "pgip_tests.ML";

use "pgip_isabelle.ML";
use "preferences.ML";
use "parsing.ML";

(use |> setmp proofs 1 |> setmp quick_and_dirty true) "proof_general_pgip.ML";
(* OLD interaction mode, not yet complete
  (use |> setmp proofs 1 |> setmp quick_and_dirty true) "proof_general_emacs.ML";
*)
