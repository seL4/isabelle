(** Pure Isabelle **)

structure Distribution =     (*filled-in by makedist*)
struct
  val version = "unidentified repository version";
  val is_official = false;
  val changelog = "";
end;

(*if true then some tools will OMIT some proofs*)
val quick_and_dirty = ref false;

print_depth 10;


(* library of general tools *)

use "General/basics.ML";
use "library.ML";
use "General/print_mode.ML";
use "General/alist.ML";
use "General/table.ML";
use "General/output.ML";
use "General/properties.ML";
use "General/markup.ML";
use "General/scan.ML";
use "General/source.ML";
use "General/symbol.ML";
use "General/seq.ML";
use "General/position.ML";
use "General/symbol_pos.ML";
use "General/antiquote.ML";
use "ML/ml_lex.ML";
use "ML/ml_parse.ML";
use "General/secure.ML";
(*^^^^^ end of basic ML bootstrap ^^^^^*)
use "General/integer.ML";
use "General/stack.ML";
use "General/queue.ML";
use "General/heap.ML";
use "General/same.ML";
use "General/ord_list.ML";
use "General/balanced_tree.ML";
use "General/graph.ML";
use "General/long_name.ML";
use "General/binding.ML";
use "General/name_space.ML";
use "General/lazy.ML";
use "General/path.ML";
use "General/url.ML";
use "General/buffer.ML";
use "General/file.ML";
use "General/xml.ML";
use "General/yxml.ML";


(* concurrency within the ML runtime *)

use "Concurrent/simple_thread.ML";
use "Concurrent/synchronized.ML";
use "Concurrent/mailbox.ML";
use "Concurrent/task_queue.ML";
use "Concurrent/future.ML";
use "Concurrent/par_list.ML";
if Multithreading.available then () else use "Concurrent/par_list_dummy.ML";


(* fundamental structures *)

use "name.ML";
use "term.ML";
use "term_ord.ML";
use "term_subst.ML";
use "old_term.ML";
use "logic.ML";
use "General/pretty.ML";
use "context.ML";
use "context_position.ML";
use "Syntax/lexicon.ML";
use "Syntax/simple_syntax.ML";
use "sorts.ML";
use "type.ML";
use "config.ML";


(* inner syntax *)

use "Syntax/ast.ML";
use "Syntax/syn_ext.ML";
use "Syntax/parser.ML";
use "Syntax/type_ext.ML";
use "Syntax/syn_trans.ML";
use "Syntax/mixfix.ML";
use "Syntax/printer.ML";
use "Syntax/syntax.ML";

use "type_infer.ML";


(* core of tactical proof system *)

use "net.ML";
use "item_net.ML";
use "envir.ML";
use "consts.ML";
use "primitive_defs.ML";
use "defs.ML";
use "sign.ML";
use "pattern.ML";
use "unify.ML";
use "theory.ML";
use "interpretation.ML";
use "proofterm.ML";
use "thm.ML";
use "more_thm.ML";
use "facts.ML";
use "pure_thy.ML";
use "drule.ML";
use "morphism.ML";
use "variable.ML";
use "conv.ML";
use "goal_display.ML";
use "tactical.ML";
use "search.ML";
use "tactic.ML";
use "meta_simplifier.ML";
use "conjunction.ML";
use "assumption.ML";
use "display.ML";
use "goal.ML";
use "axclass.ML";


(* Isar -- Intelligible Semi-Automated Reasoning *)

(*proof context*)
use "Isar/object_logic.ML";
use "Isar/rule_cases.ML";
use "Isar/auto_bind.ML";
use "Isar/local_syntax.ML";
use "Isar/proof_context.ML";
use "Isar/local_defs.ML";

(*proof term operations*)
use "Proof/reconstruct.ML";
use "Proof/proof_syntax.ML";
use "Proof/proof_rewrite_rules.ML";
use "Proof/proofchecker.ML";

(*outer syntax*)
use "Isar/outer_lex.ML";
use "Isar/outer_keyword.ML";
use "Isar/outer_parse.ML";
use "Isar/value_parse.ML";
use "Isar/args.ML";

(*ML support*)
use "ML/ml_syntax.ML";
use "ML/ml_env.ML";
use "Isar/runtime.ML";
if ml_system = "polyml-experimental"
then use "ML/ml_compiler_polyml-5.3.ML"
else use "ML/ml_compiler.ML";
use "ML/ml_context.ML";

(*theory sources*)
use "Thy/thy_header.ML";
use "Thy/thy_load.ML";
use "Thy/html.ML";
use "Thy/latex.ML";
use "Thy/present.ML";

(*basic proof engine*)
use "Isar/proof_display.ML";
use "Isar/attrib.ML";
use "ML/ml_antiquote.ML";
use "Isar/context_rules.ML";
use "Isar/skip_proof.ML";
use "Isar/method.ML";
use "Isar/proof.ML";
use "ML/ml_thms.ML";
use "Isar/element.ML";

(*derived theory and proof elements*)
use "Isar/calculation.ML";
use "Isar/obtain.ML";

(*local theories and targets*)
use "Isar/local_theory.ML";
use "Isar/overloading.ML";
use "Isar/locale.ML";
use "Isar/class_target.ML";
use "Isar/theory_target.ML";
use "Isar/expression.ML";
use "Isar/class.ML";

use "simplifier.ML";

(*executable theory content*)
use "Isar/code.ML";

(*specifications*)
use "Isar/spec_parse.ML";
use "Isar/specification.ML";
use "Isar/constdefs.ML";

(*toplevel transactions*)
use "Isar/proof_node.ML";
use "Isar/toplevel.ML";

(*theory syntax*)
use "Thy/term_style.ML";
use "Thy/thy_output.ML";
use "Thy/thy_syntax.ML";
use "old_goals.ML";
use "Isar/outer_syntax.ML";
use "Thy/thy_info.ML";
use "Isar/isar_document.ML";

(*theory and proof operations*)
use "Isar/rule_insts.ML";
use "Thy/thm_deps.ML";
use "Isar/isar_cmd.ML";
use "Isar/isar_syn.ML";

use "subgoal.ML";

use "Proof/extraction.ML";


(* Isabelle/Isar system *)

use "System/session.ML";
use "System/isar.ML";
use "System/isabelle_process.ML";


(* miscellaneous tools and packages for Pure Isabelle *)

use "Tools/named_thms.ML";

use "Tools/xml_syntax.ML";

use "Tools/find_theorems.ML";
use "Tools/find_consts.ML";

use "codegen.ML";


(* configuration for Proof General *)

use "ProofGeneral/pgip_types.ML";
use "ProofGeneral/pgml.ML";
use "ProofGeneral/pgip_markup.ML";
use "ProofGeneral/pgip_input.ML";
use "ProofGeneral/pgip_output.ML";
use "ProofGeneral/pgip.ML";

use "ProofGeneral/pgip_isabelle.ML";

use "ProofGeneral/preferences.ML";

use "ProofGeneral/pgip_parser.ML";

use "ProofGeneral/pgip_tests.ML";

use "ProofGeneral/proof_general_pgip.ML";
use "ProofGeneral/proof_general_emacs.ML";


use "pure_setup.ML";

