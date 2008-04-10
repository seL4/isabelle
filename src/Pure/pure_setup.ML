(*  Title:      Pure/pure_setup.ML
    ID:         $Id$
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

use_thy "CPure";
structure CPure = struct val thy = theory "CPure" end;


(* ML toplevel pretty printing *)

install_pp (make_pp ["Thm", "thm"] ProofDisplay.pprint_thm);
install_pp (make_pp ["Thm", "cterm"] ProofDisplay.pprint_cterm);
install_pp (make_pp ["Thm", "ctyp"] ProofDisplay.pprint_ctyp);
install_pp (make_pp ["Context", "theory"] Context.pprint_thy);
install_pp (make_pp ["Context", "proof"] ProofDisplay.pprint_context);
install_pp (make_pp ["Syntax", "ast"] Syntax.pprint_ast);
install_pp (make_pp ["typ"] (ProofDisplay.pprint_typ Pure.thy));
install_pp (make_pp ["Path", "T"] (Pretty.pprint o Pretty.str o quote o Path.implode));
install_pp (make_pp ["File", "ident"] (Pretty.pprint o Pretty.str o quote o File.rep_ident));


(* misc *)

val cd = File.cd o Path.explode;
ml_prompts "ML> " "ML# ";

Proofterm.proofs := 0;
