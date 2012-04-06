(** Pure Isabelle **)

structure Distribution =     (*filled-in by makedist*)
struct
  val version = "unidentified repository version";
  val is_official = false;
  val changelog = "";
end;

(*if true then some tools will OMIT some proofs*)
val quick_and_dirty = Unsynchronized.ref false;

print_depth 10;


(* library of general tools *)

use "General/basics.ML";
use "library.ML";
use "General/print_mode.ML";
use "General/alist.ML";
use "General/table.ML";

use "Concurrent/simple_thread.ML";

use "Concurrent/synchronized.ML";
if Multithreading.available then ()
else use "Concurrent/synchronized_sequential.ML";

use "General/properties.ML";
use "General/output.ML";
use "General/timing.ML";
use "PIDE/markup.ML";
use "PIDE/isabelle_markup.ML";
fun legacy_feature s = warning (Markup.markup Isabelle_Markup.legacy ("Legacy feature! " ^ s));
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
use "General/linear_set.ML";
use "General/buffer.ML";
use "General/pretty.ML";
use "General/path.ML";
use "General/url.ML";
use "General/file.ML";
use "General/long_name.ML";
use "General/binding.ML";

use "General/sha1.ML";
if ML_System.is_polyml then use "General/sha1_polyml.ML" else ();

use "PIDE/xml.ML";
use "PIDE/yxml.ML";


(* concurrency within the ML runtime *)

use "Concurrent/single_assignment.ML";
if Multithreading.available then ()
else use "Concurrent/single_assignment_sequential.ML";

if ML_System.is_smlnj then () else use "Concurrent/time_limit.ML";

if Multithreading.available
then use "Concurrent/bash.ML"
else use "Concurrent/bash_sequential.ML";

use "Concurrent/par_exn.ML";
use "Concurrent/task_queue.ML";
use "Concurrent/future.ML";

use "Concurrent/lazy.ML";
if Multithreading.available then ()
else use "Concurrent/lazy_sequential.ML";

use "Concurrent/par_list.ML";
if Multithreading.available then ()
else use "Concurrent/par_list_sequential.ML";

use "Concurrent/mailbox.ML";
use "Concurrent/cache.ML";


(* fundamental structures *)

use "name.ML";
use "term.ML";
use "context.ML";
use "config.ML";
use "context_position.ML";


(* inner syntax *)

use "Syntax/term_position.ML";
use "Syntax/lexicon.ML";
use "Syntax/ast.ML";
use "Syntax/syntax_ext.ML";
use "Syntax/parser.ML";
use "Syntax/syntax_trans.ML";
use "Syntax/mixfix.ML";
use "Syntax/printer.ML";
use "Syntax/syntax.ML";


(* core of tactical proof system *)

use "term_ord.ML";
use "term_subst.ML";
use "term_xml.ML";
use "General/name_space.ML";
use "sorts.ML";
use "type.ML";
use "logic.ML";
use "Syntax/simple_syntax.ML";
use "net.ML";
use "item_net.ML";
use "envir.ML";
use "consts.ML";
use "primitive_defs.ML";
use "defs.ML";
use "sign.ML";
use "term_sharing.ML";
use "pattern.ML";
use "unify.ML";
use "theory.ML";
use "interpretation.ML";
use "proofterm.ML";
use "thm.ML";
use "more_thm.ML";
use "facts.ML";
use "global_theory.ML";
use "pure_thy.ML";
use "drule.ML";
use "morphism.ML";
use "variable.ML";
use "conv.ML";
use "goal_display.ML";
use "tactical.ML";
use "search.ML";
use "tactic.ML";
use "raw_simplifier.ML";
use "conjunction.ML";
use "assumption.ML";
use "display.ML";
use "goal.ML";


(* Isar -- Intelligible Semi-Automated Reasoning *)

(*proof context*)
use "Isar/object_logic.ML";
use "Isar/rule_cases.ML";
use "Isar/auto_bind.ML";
use "type_infer.ML";
use "Syntax/local_syntax.ML";
use "Isar/proof_context.ML";
use "type_infer_context.ML";
use "Syntax/syntax_phases.ML";
use "Isar/local_defs.ML";

(*proof term operations*)
use "Proof/reconstruct.ML";
use "Proof/proof_syntax.ML";
use "Proof/proof_rewrite_rules.ML";
use "Proof/proof_checker.ML";

(*outer syntax*)
use "Isar/token.ML";
use "Isar/keyword.ML";
use "Isar/parse.ML";
use "Isar/args.ML";

(*ML support*)
use "ML/ml_syntax.ML";
use "ML/ml_env.ML";
use "Isar/runtime.ML";
use "ML/ml_compiler.ML";
if ML_System.name = "polyml-5.2.1" orelse ML_System.is_smlnj then ()
else use "ML/ml_compiler_polyml-5.3.ML";
use "ML/ml_context.ML";

(*theory sources*)
use "Thy/thy_header.ML";
use "Thy/html.ML";
use "Thy/latex.ML";

(*basic proof engine*)
use "Isar/proof_display.ML";
use "Isar/attrib.ML";
use "ML/ml_antiquote.ML";
use "Isar/context_rules.ML";
use "Isar/skip_proof.ML";
use "Isar/method.ML";
use "Isar/proof.ML";
use "Isar/element.ML";

(*derived theory and proof elements*)
use "Isar/calculation.ML";
use "Isar/obtain.ML";

(*local theories and targets*)
use "Isar/local_theory.ML";
use "Isar/locale.ML";
use "Isar/generic_target.ML";
use "Isar/overloading.ML";
use "axclass.ML";
use "Isar/class.ML";
use "Isar/named_target.ML";
use "Isar/expression.ML";
use "Isar/class_declaration.ML";
use "Isar/bundle.ML";

use "simplifier.ML";

(*executable theory content*)
use "Isar/code.ML";

(*specifications*)
use "Isar/parse_spec.ML";
use "Isar/spec_rules.ML";
use "Isar/specification.ML";
use "Isar/typedecl.ML";
use "ML/ml_thms.ML";

(*toplevel transactions*)
use "Isar/proof_node.ML";
use "Isar/toplevel.ML";

(*theory documents*)
use "System/isabelle_system.ML";
use "Thy/term_style.ML";
use "Thy/thy_output.ML";
use "Thy/thy_syntax.ML";
use "Isar/outer_syntax.ML";
use "Thy/present.ML";
use "Thy/thy_load.ML";
use "Thy/thy_info.ML";
use "PIDE/command.ML";
use "PIDE/document.ML";
use "Thy/rail.ML";

(*theory and proof operations*)
use "Isar/rule_insts.ML";
use "Thy/thm_deps.ML";
use "Isar/isar_cmd.ML";
use "Isar/isar_syn.ML";

use "subgoal.ML";

use "Proof/extraction.ML";


(* Isabelle/Isar system *)

use "System/session.ML";
use "System/system_channel.ML";
use "System/isabelle_process.ML";
use "System/invoke_scala.ML";
use "PIDE/protocol.ML";
use "System/isar.ML";


(* miscellaneous tools and packages for Pure Isabelle *)

use "Tools/named_thms.ML";

use "Tools/xml_syntax.ML";

use "Tools/find_theorems.ML";
use "Tools/find_consts.ML";


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

