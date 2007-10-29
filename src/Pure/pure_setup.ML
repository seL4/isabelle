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

use_thy "Pure";
structure Pure = struct val thy = theory "Pure" end;

Context.add_setup
 (Sign.del_modesyntax_i Syntax.mode_default PureThy.appl_syntax #>
  Sign.add_syntax_i PureThy.applC_syntax);
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
