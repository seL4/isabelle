(*  Title:      Pure/ProofGeneral/ROOT.ML
    ID:         $Id$
    Author:     David Aspinall

Proof General interface for Isabelle, both the traditional Emacs version,
and PGIP experiments.
*)

use "pgip_types.ML";
use "pgml.ML";
use "pgip_markup.ML";
use "pgip_input.ML";
use "pgip_output.ML";
use "pgip.ML";

use "pgip_isabelle.ML";
use "pgml_isabelle.ML";
(use |> setmp proofs 1 |> setmp quick_and_dirty true) "preferences.ML";
use "pgip_parser.ML";

use "parsing.ML";   (* old version *)

use "pgip_tests.ML";

use "proof_general_pgip.ML";
use "proof_general_emacs.ML";

