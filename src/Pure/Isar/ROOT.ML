(*  Title:      Pure/Isar/ROOT.ML
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

(*proof term operations*)
use "../Proof/reconstruct.ML";
use "../Proof/proof_syntax.ML";
use "../Proof/proof_rewrite_rules.ML";
use "../Proof/proofchecker.ML";

(*outer syntax*)
use "outer_lex.ML";
use "outer_keyword.ML";
use "outer_parse.ML";
use "value_parse.ML";
use "args.ML";

(*ML support*)
use "../ML/ml_syntax.ML";
use "../ML/ml_env.ML";
if ml_system = "polyml-experimental"
then use "../ML/ml_compiler_polyml-5.3.ML"
else use "../ML/ml_compiler.ML";
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
use "../ML/ml_antiquote.ML";
use "context_rules.ML";
use "skip_proof.ML";
use "method.ML";
use "proof.ML";
use "../ML/ml_thms.ML";
use "element.ML";

(*derived theory and proof elements*)
use "calculation.ML";
use "obtain.ML";

(*local theories and targets*)
use "local_theory.ML";
use "overloading.ML";
use "locale.ML";
use "class_target.ML";
use "theory_target.ML";
use "expression.ML";
use "class.ML";

(*complex proof machineries*)
use "../simplifier.ML";

(*executable theory content*)
use "code.ML";

(*specifications*)
use "spec_parse.ML";
use "specification.ML";
use "constdefs.ML";

(*toplevel transactions*)
use "proof_node.ML";
use "toplevel.ML";

(*theory syntax*)
use "../Thy/term_style.ML";
use "../Thy/thy_output.ML";
use "../Thy/thy_syntax.ML";
use "../old_goals.ML";
use "outer_syntax.ML";
use "../Thy/thy_info.ML";
use "isar_document.ML";

(*theory and proof operations*)
use "rule_insts.ML";
use "../Thy/thm_deps.ML";
use "isar_cmd.ML";
use "isar_syn.ML";
