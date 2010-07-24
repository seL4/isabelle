(*  Title:      Pure/pure_setup.ML
    Author:     Makarius

Pure theory and ML toplevel setup.
*)

(* the Pure theories *)

Context.>> (Context.map_theory
 (Outer_Syntax.process_file (Path.explode "Pure.thy") #>
  Theory.end_theory));
structure Pure = struct val thy = ML_Context.the_global_context () end;
Context.set_thread_data NONE;
Thy_Info.register_theory Pure.thy;


(* ML toplevel pretty printing *)

if String.isPrefix "smlnj" ml_system then ()
else toplevel_pp ["String", "string"] "ML_Syntax.pretty_string";

toplevel_pp ["Pretty", "T"] "(fn _: Pretty.T => Pretty.str \"<pretty>\")";
toplevel_pp ["Task_Queue", "task"] "Pretty.str o Task_Queue.str_of_task";
toplevel_pp ["Task_Queue", "group"] "Pretty.str o Task_Queue.str_of_group";
toplevel_pp ["Position", "T"] "Pretty.position";
toplevel_pp ["Binding", "binding"] "Pretty.str o quote o Binding.str_of";
toplevel_pp ["Thm", "thm"] "Proof_Display.pp_thm";
toplevel_pp ["Thm", "cterm"] "Proof_Display.pp_cterm";
toplevel_pp ["Thm", "ctyp"] "Proof_Display.pp_ctyp";
toplevel_pp ["typ"] "Proof_Display.pp_typ Pure.thy";
toplevel_pp ["Context", "theory"] "Context.pretty_thy";
toplevel_pp ["Context", "theory_ref"] "Context.pretty_thy o Theory.deref";
toplevel_pp ["Context", "Proof", "context"] "Proof_Display.pp_context";
toplevel_pp ["Syntax", "ast"] "Syntax.pretty_ast";
toplevel_pp ["Path", "T"] "Pretty.str o quote o Path.implode";
toplevel_pp ["File", "ident"] "Pretty.str o quote o File.rep_ident";
toplevel_pp ["Proof", "state"] "(fn _: Proof.state => Pretty.str \"<Proof.state>\")";
toplevel_pp ["Toplevel", "state"] "Toplevel.pretty_abstract";

if ml_system = "polyml-5.3.0"
then use "ML-Systems/install_pp_polyml-5.3.ML"
else if String.isPrefix "polyml" ml_system
then use "ML-Systems/install_pp_polyml.ML"
else ();

if ml_system = "polyml-5.0" orelse ml_system = "polyml-5.1" then
  Secure.use_text ML_Parse.global_context (0, "") false
    "PolyML.Compiler.maxInlineSize := 20"
else ();


(* ML toplevel use commands *)

fun use name = Toplevel.program (fn () => Thy_Load.use_ml (Path.explode name));

fun use_thys name = Toplevel.program (fn () => Thy_Info.use_thys name);
fun use_thy name = Toplevel.program (fn () => Thy_Info.use_thy name);


(* misc *)

val cd = File.cd o Path.explode;

Proofterm.proofs := 0;
