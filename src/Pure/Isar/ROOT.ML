(*  Title:      Pure/Isar/ROOT.ML
    ID:         $Id$
    Author:     Markus Wenzel, TU Muenchen

Isar -- Intelligible Semi-Automated Reasoning for Isabelle.
*)

(*proof engine*)
use "proof_context.ML";
use "proof.ML";
use "proof_data.ML";
use "args.ML";
use "attrib.ML";
use "method.ML";

(*outer syntax*)
use "outer_lex.ML";
use "outer_parse.ML";

(*interactive subsystem*)
use "proof_history.ML";
use "toplevel.ML";
use "outer_syntax.ML";

(*theory operations and syntax*)
use "isar_thy.ML";
use "isar_cmd.ML";
use "isar_syn.ML";
