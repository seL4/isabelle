(*  Title:      Pure/Isar/ROOT.ML
    ID:         $Id$
    Author:     Markus Wenzel, TU Muenchen

Isar -- Intelligible Semi-Automated Reasoning for Isabelle.
*)

(*basic proof engine*)
use "object_logic.ML";
use "auto_bind.ML";
use "rule_cases.ML";
use "proof_context.ML";
use "context_rules.ML";
use "args.ML";
use "attrib.ML";
use "locale.ML";
use "proof.ML";
use "method.ML";
use "proof_history.ML";
use "net_rules.ML";
use "induct_attrib.ML";

(*derived proof elements*)
use "calculation.ML";
use "obtain.ML";
use "skip_proof.ML";

(*outer syntax*)
use "antiquote.ML";
use "outer_parse.ML";
use "outer_keyword.ML";

(*toplevel environment*)
use "toplevel.ML";

(*theory presentation*)
use "term_style.ML";
use "isar_output.ML";

(*theory syntax*)
use "thy_header.ML";
use "session.ML";
use "outer_syntax.ML";

(*theory and proof operations*)
use "isar_thy.ML";
use "constdefs.ML";
use "../simplifier.ML";
use "find_theorems.ML";
use "isar_cmd.ML";
use "isar_syn.ML";
