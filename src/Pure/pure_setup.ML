(*  Title:      Pure/pure_setup.ML
    Author:     Makarius

Pure theory and ML toplevel setup.
*)

(* the Pure theory *)

Context.>> (Context.map_theory
 (Outer_Syntax.process_file (Path.explode "Pure.thy") #>
  Theory.end_theory));

structure Pure = struct val thy = ML_Context.the_global_context () end;

Context.set_thread_data NONE;
Thy_Info.register_thy Pure.thy;


(* ML toplevel pretty printing *)

toplevel_pp ["Pretty", "T"] "(fn _: Pretty.T => Pretty.str \"<pretty>\")";
toplevel_pp ["Task_Queue", "task"] "Pretty.str o Task_Queue.str_of_task";
toplevel_pp ["Task_Queue", "group"] "Pretty.str o Task_Queue.str_of_group";
toplevel_pp ["Position", "T"] "Pretty.position";
toplevel_pp ["Binding", "binding"] "Pretty.str o Binding.print";
toplevel_pp ["Thm", "thm"] "Proof_Display.pp_thm";
toplevel_pp ["Thm", "cterm"] "Proof_Display.pp_cterm";
toplevel_pp ["Thm", "ctyp"] "Proof_Display.pp_ctyp";
toplevel_pp ["typ"] "Proof_Display.pp_typ Pure.thy";
toplevel_pp ["Context", "theory"] "Context.pretty_thy";
toplevel_pp ["Context", "theory_ref"] "Context.pretty_thy o Theory.deref";
toplevel_pp ["Context", "Proof", "context"] "Proof_Display.pp_context";
toplevel_pp ["Ast", "ast"] "Ast.pretty_ast";
toplevel_pp ["Path", "T"] "Path.pretty";
toplevel_pp ["SHA1", "digest"] "Pretty.str o quote o SHA1.rep";
toplevel_pp ["Proof", "state"] "(fn _: Proof.state => Pretty.str \"<Proof.state>\")";
toplevel_pp ["Toplevel", "state"] "Toplevel.pretty_abstract";

if ML_System.name = "polyml-5.2.1"
then use "ML/install_pp_polyml.ML"
else if ML_System.is_polyml
then use "ML/install_pp_polyml-5.3.ML"
else ();


(* ML toplevel use commands *)

fun use name = Toplevel.program (fn () => Thy_Load.use_ml (Path.explode name));

fun use_thys name = Toplevel.program (fn () => Thy_Info.use_thys name);
fun use_thy name = Toplevel.program (fn () => Thy_Info.use_thy name);


(* misc *)

val cd = File.cd o Path.explode;

Proofterm.proofs := 0;

