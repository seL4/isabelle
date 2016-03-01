(*** Isabelle/Pure bootstrap from "RAW" environment ***)

(** bootstrap phase 0: towards secure ML barrier *)

structure Distribution =     (*filled-in by makedist*)
struct
  val version = "unidentified repository version";
  val is_identified = false;
  val is_official = false;
end;


(* library of general tools *)

use "General/basics.ML";
use "library.ML";
use "General/print_mode.ML";
use "General/alist.ML";
use "General/table.ML";

use "Concurrent/synchronized.ML";
use "Concurrent/counter.ML";
use "Concurrent/random.ML";

use "General/properties.ML";
use "General/output.ML";
use "PIDE/markup.ML";
use "General/scan.ML";
use "General/source.ML";
use "General/symbol.ML";
use "General/position.ML";
use "General/symbol_pos.ML";
use "General/input.ML";
use "General/antiquote.ML";
use "ML/ml_lex.ML";
use "ML/ml_parse.ML";
use "General/secure.ML";

val use_text = Secure.use_text;
val use_file = Secure.use_file;

local
  fun use_ opt_debug file =
    Position.setmp_thread_data (Position.file_only file)
      (fn () =>
        Secure.use_file ML_Parse.global_context
          {verbose = true, debug = use_debug_option opt_debug} file
        handle ERROR msg => (writeln msg; error "ML error")) ();
in
  val use = use_ NONE;
  val use_debug = use_ (SOME true);
  val use_no_debug = use_ (SOME false);
end;



(** bootstrap phase 1: towards ML within Isar context *)

(* library of general tools *)

use "General/integer.ML";
use "General/stack.ML";
use "General/queue.ML";
use "General/heap.ML";
use "General/same.ML";
use "General/ord_list.ML";
use "General/balanced_tree.ML";
use "General/linear_set.ML";
use "General/buffer.ML";
use "General/pretty.ML";
use "PIDE/xml.ML";
use "General/path.ML";
use "General/url.ML";
use "General/file.ML";
use "General/long_name.ML";
use "General/binding.ML";
use "General/socket_io.ML";
use "General/seq.ML";
use "General/timing.ML";

use "General/sha1.ML";
use "General/sha1_polyml.ML";
use "General/sha1_samples.ML";

use "PIDE/yxml.ML";
use "PIDE/document_id.ML";

use "General/change_table.ML";
use "General/graph.ML";


(* fundamental structures *)

use "name.ML";
use "term.ML";
use "context.ML";
use "context_position.ML";
use "System/options.ML";
use "config.ML";


(* concurrency within the ML runtime *)

use "ML/exn_properties.ML";

if ML_System.name = "polyml-5.6"
then use "ML/ml_statistics.ML"
else use "ML/ml_statistics_dummy.ML";

use "Concurrent/standard_thread.ML";
use "Concurrent/single_assignment.ML";

if ML_System.platform_is_windows
then use "Concurrent/bash_windows.ML"
else use "Concurrent/bash.ML";

use "Concurrent/par_exn.ML";
use "Concurrent/task_queue.ML";
use "Concurrent/future.ML";
use "Concurrent/event_timer.ML";
use "Concurrent/time_limit.ML";
use "Concurrent/lazy.ML";
use "Concurrent/par_list.ML";

use "Concurrent/mailbox.ML";
use "Concurrent/cache.ML";

use "PIDE/active.ML";


(* inner syntax *)

use "Syntax/type_annotation.ML";
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
use "General/completion.ML";
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
use "sign.ML";
use "defs.ML";
use "term_sharing.ML";
use "pattern.ML";
use "unify.ML";
use "theory.ML";
use "proofterm.ML";
use "thm.ML";
use "more_pattern.ML";
use "more_unify.ML";
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


(* Isar -- Intelligible Semi-Automated Reasoning *)

(*ML support and global execution*)
use "ML/ml_syntax.ML";
use "ML/ml_env.ML";
use "ML/ml_options.ML";
use "ML/exn_output.ML";
use "ML/ml_options.ML";
use "Isar/runtime.ML";
use "PIDE/execution.ML";
use "ML/ml_compiler.ML";

use "skip_proof.ML";
use "goal.ML";

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

(*outer syntax*)
use "Isar/keyword.ML";
use "Isar/token.ML";
use "Isar/parse.ML";
use "Isar/args.ML";

(*theory specifications*)
use "Isar/local_theory.ML";
use "Thy/thy_header.ML";
use "PIDE/command_span.ML";
use "Thy/thy_syntax.ML";
use "Thy/markdown.ML";
use "Thy/html.ML";
use "Thy/latex.ML";

(*ML with context and antiquotations*)
use "ML/ml_context.ML";
use "ML/ml_antiquotation.ML";

local
  fun use_ opt_debug file =
    let val flags = ML_Compiler.debug_flags opt_debug |> ML_Compiler.verbose true in
      ML_Context.eval_file flags (Path.explode file)
        handle ERROR msg => (writeln msg; error "ML error")
    end;
in

val use = use_ NONE;
val use_debug = use_ (SOME true);
val use_no_debug = use_ (SOME false);

end;



(** bootstrap phase 2: towards Pure.thy and final ML toplevel setup *)

(*basic proof engine*)
use "par_tactical.ML";
use "Isar/proof_display.ML";
use "Isar/attrib.ML";
use "Isar/context_rules.ML";
use "Isar/method.ML";
use "Isar/proof.ML";
use "Isar/element.ML";
use "Isar/obtain.ML";
use "Isar/subgoal.ML";

(*local theories and targets*)
use "Isar/locale.ML";
use "Isar/generic_target.ML";
use "Isar/overloading.ML";
use "axclass.ML";
use "Isar/class.ML";
use "Isar/named_target.ML";
use "Isar/expression.ML";
use "Isar/interpretation.ML";
use "Isar/class_declaration.ML";
use "Isar/bundle.ML";
use "Isar/experiment.ML";

use "simplifier.ML";
use "Tools/plugin.ML";

(*executable theory content*)
use "Isar/code.ML";

(*specifications*)
use "Isar/parse_spec.ML";
use "Isar/spec_rules.ML";
use "Isar/specification.ML";
use "Isar/typedecl.ML";

(*toplevel transactions*)
use "Isar/proof_node.ML";
use "Isar/toplevel.ML";

(*proof term operations*)
use "Proof/reconstruct.ML";
use "Proof/proof_syntax.ML";
use "Proof/proof_rewrite_rules.ML";
use "Proof/proof_checker.ML";
use "Proof/extraction.ML";

(*theory documents*)
use "System/isabelle_system.ML";
use "Thy/term_style.ML";
use "Isar/outer_syntax.ML";
use "Thy/thy_output.ML";
use "Thy/document_antiquotations.ML";
use "General/graph_display.ML";
use "Thy/present.ML";
use "pure_syn.ML";
use "PIDE/command.ML";
use "PIDE/query_operation.ML";
use "PIDE/resources.ML";
use "Thy/thy_info.ML";
use "PIDE/session.ML";
use "PIDE/protocol_message.ML";
use "PIDE/document.ML";

(*theory and proof operations*)
use "Isar/isar_cmd.ML";


(* Isabelle/Isar system *)

use "System/command_line.ML";
use "System/system_channel.ML";
use "System/message_channel.ML";
use "System/isabelle_process.ML";
use "System/invoke_scala.ML";
use "PIDE/protocol.ML";


(* miscellaneous tools and packages for Pure Isabelle *)

use "Tools/build.ML";
use "Tools/named_thms.ML";

structure Output: OUTPUT = Output;  (*seal system channels!*)


use "ML/install_pp_polyml.ML";


(* the Pure theory *)

use "ML/ml_file.ML";
Runtime.toplevel_program (fn () => Thy_Info.use_thy ("Pure", Position.none));
Context.set_thread_data NONE;
structure Pure = struct val thy = Thy_Info.pure_theory () end;


(* ML toplevel commands *)

fun use_thys args =
  Runtime.toplevel_program (fn () => Thy_Info.use_thys (map (rpair Position.none) args));
val use_thy = use_thys o single;

val cd = File.cd o Path.explode;

Proofterm.proofs := 0;
