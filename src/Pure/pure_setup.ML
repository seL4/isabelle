(*  Title:      Pure/pure_setup.ML
    Author:     Makarius

Pure theory and ML toplevel setup.
*)

(* ML toplevel use commands *)

fun use name          = Toplevel.program (fn () => ThyInfo.use name);
fun use_thys name     = Toplevel.program (fn () => ThyInfo.use_thys name);
fun use_thy name      = Toplevel.program (fn () => ThyInfo.use_thy name);
fun time_use name     = Toplevel.program (fn () => ThyInfo.time_use name);
fun time_use_thy name = Toplevel.program (fn () => ThyInfo.time_use_thy name);


(* the Pure theories *)

val theory = ThyInfo.get_theory;

Context.>> (Context.map_theory
 (OuterSyntax.process_file (Path.explode "Pure.thy") #>
  Theory.end_theory));
structure Pure = struct val thy = ML_Context.the_global_context () end;
Context.set_thread_data NONE;
ThyInfo.register_theory Pure.thy;


(* ML toplevel pretty printing *)

toplevel_pp ["Task_Queue", "task"] "Pretty.str o Task_Queue.str_of_task";
toplevel_pp ["Task_Queue", "group"] "Pretty.str o Task_Queue.str_of_group";
toplevel_pp ["Position", "T"] "Pretty.position";
toplevel_pp ["Binding", "binding"] "Pretty.str o quote o Binding.str_of";
toplevel_pp ["Thm", "thm"] "ProofDisplay.pp_thm";
toplevel_pp ["Thm", "cterm"] "ProofDisplay.pp_cterm";
toplevel_pp ["Thm", "ctyp"] "ProofDisplay.pp_ctyp";
toplevel_pp ["typ"] "ProofDisplay.pp_typ Pure.thy";
toplevel_pp ["Context", "theory"] "Context.pretty_thy";
toplevel_pp ["Context", "theory_ref"] "Context.pretty_thy o Theory.deref";
toplevel_pp ["Context", "proof"] "ProofDisplay.pp_context";
toplevel_pp ["Syntax", "ast"] "Syntax.pretty_ast";
toplevel_pp ["Path", "T"] "Pretty.str o quote o Path.implode";
toplevel_pp ["File", "ident"] "Pretty.str o quote o File.rep_ident";

if File.exists (Path.explode ("ML-Systems/install_pp_" ^ ml_system ^ ".ML"))
then use ("ML-Systems/install_pp_" ^ ml_system ^ ".ML")
else if String.isPrefix "polyml" ml_system
then use "ML-Systems/install_pp_polyml.ML"
else ();


(* misc *)

val cd = File.cd o Path.explode;

Proofterm.proofs := 0;
