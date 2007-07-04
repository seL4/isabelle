(*  Title:      Pure/ProofGeneral/ROOT.ML
    ID:         $Id$
    Author:     David Aspinall

Proof General interface for Isabelle.
*)

use "pgip_types.ML";
use "pgip_markup.ML";
use "pgip_input.ML";
use "pgip_output.ML";
use "pgip.ML";
use "pgml.ML";

use "pgip_isabelle.ML";
(*use "pgml_isabelle.ML";*)
use "preferences.ML";
use "parsing.ML";

use "pgip_tests.ML";

(use |> setmp proofs 1 |> setmp quick_and_dirty true) "proof_general_pgip.ML";
(use |> setmp proofs 1 |> setmp quick_and_dirty true) "proof_general_emacs.ML";

(* desirable to have tests on UI connection:
  use "pgip_isabelle_tests.ML"
*)
