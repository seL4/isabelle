(*  Title:      Pure/Isar/ROOT.ML
    ID:         $Id$
    Author:     Markus Wenzel, TU Muenchen

Isar -- Intelligible Semi-Automated Reasoning for Isabelle.
*)

(*proof context*)
use "object_logic.ML";
use "rule_cases.ML";
use "auto_bind.ML";
use "local_syntax.ML";
use "proof_context.ML";
use "local_defs.ML";

(*outer syntax*)
use "outer_lex.ML";
use "args.ML";
use "outer_parse.ML";
use "outer_keyword.ML";
use "antiquote.ML";
use "../ML/ml_context.ML";

(*theory sources*)
use "../Thy/thy_header.ML";
use "../Thy/thy_load.ML";
use "../Thy/html.ML";
use "../Thy/latex.ML";
use "../Thy/present.ML";

(*basic proof engine*)
use "proof_display.ML";
use "attrib.ML";
use "context_rules.ML";
use "skip_proof.ML";
use "method.ML";
use "proof.ML";
use "element.ML";
use "net_rules.ML";

(*derived theory and proof elements*)
use "calculation.ML";
use "obtain.ML";

(*local theories and target primitives*)
use "local_theory.ML";
use "overloading.ML";
use "locale.ML";
use "class.ML";

(*executable theory content*)
use "code_unit.ML";
use "code.ML";

(*local theories and specifications*)
use "theory_target.ML";
use "subclass.ML";
use "spec_parse.ML";
use "specification.ML";
use "instance.ML";
use "constdefs.ML";

(*toplevel transactions*)
use "proof_history.ML";
use "toplevel.ML";

(*theory syntax*)
use "../Thy/term_style.ML";
use "../Thy/thy_output.ML";
use "../old_goals.ML";
use "outer_syntax.ML";
use "../Thy/thy_info.ML";
use "session.ML";
use "isar.ML";
use "../Thy/thy_edit.ML";

(*theory and proof operations*)
use "rule_insts.ML";
use "../simplifier.ML";
use "../Thy/thm_deps.ML";
use "find_theorems.ML";
use "isar_cmd.ML";
use "isar_syn.ML";
