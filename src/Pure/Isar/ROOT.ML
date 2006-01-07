(*  Title:      Pure/Isar/ROOT.ML
    ID:         $Id$
    Author:     Markus Wenzel, TU Muenchen

Isar -- Intelligible Semi-Automated Reasoning for Isabelle.
*)

(*basic proof engine*)
use "object_logic.ML";
use "rule_cases.ML";
use "auto_bind.ML";
use "proof_context.ML";
use "proof_display.ML";
use "context_rules.ML";
use "args.ML";
use "attrib.ML";
use "skip_proof.ML";
use "method.ML";
use "proof.ML";
use "element.ML";
use "net_rules.ML";
use "induct_attrib.ML";

(*derived theory and proof elements*)
use "specification.ML";
use "constdefs.ML";
use "obtain.ML";
use "locale.ML";
use "calculation.ML";

(*outer syntax*)
use "antiquote.ML";
use "outer_parse.ML";
use "outer_keyword.ML";

(*toplevel environment*)
use "proof_history.ML";
use "toplevel.ML";

(*theory presentation*)
use "term_style.ML";
use "isar_output.ML";

(*theory syntax*)
use "thy_header.ML";
use "session.ML";
use "../old_goals.ML";
use "outer_syntax.ML";

(*theory and proof operations*)
use "../simplifier.ML";
use "find_theorems.ML";
use "isar_thy.ML";
use "isar_cmd.ML";
use "isar_syn.ML";
