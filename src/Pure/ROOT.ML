(*  Title:      Pure/ROOT.ML
    ID:         $Id$

Pure Isabelle.
*)

val banner = "Pure Isabelle";
val version = "Isabelle repository version";    (*filled in automatically!*)


print_depth 10;

(*fake hiding of private structures*)
structure Hidden = struct end;

(*basic tools*)
use "library.ML";
cd "General"; use "ROOT.ML"; cd "..";

(*fundamental structures*)
use "term.ML";
use "General/pretty.ML";
use "sorts.ML";
use "type.ML";
use "context.ML";
use "compress.ML";

(*inner syntax module*)
cd "Syntax"; use "ROOT.ML"; cd "..";

(*core of tactical proof system*)
use "type_infer.ML";
use "sign.ML";
use "envir.ML";
use "pattern.ML";
use "unify.ML";
use "net.ML";
use "logic.ML";
use "defs.ML";
use "theory.ML";
use "proofterm.ML";
use "thm.ML";
use "display.ML";
use "fact_index.ML";
use "pure_thy.ML";
use "drule.ML";
use "tctical.ML";
use "search.ML";
use "meta_simplifier.ML";
use "tactic.ML";

(*proof term operations*)
use "Proof/reconstruct.ML";
use "Proof/proof_syntax.ML";
use "Proof/proof_rewrite_rules.ML";
use "Proof/proofchecker.ML";

(*theory auto loader database*)
use "Thy/thy_load.ML";
use "Thy/thy_info.ML";

(*theory syntax -- old format*)
use "Thy/thy_scan.ML";
use "Thy/thy_parse.ML";
use "Thy/thy_syn.ML";

(*theory syntax -- new format*)
use "Isar/outer_lex.ML";

(*theory presentation*)
use "Thy/html.ML";
use "Thy/latex.ML";
use "Thy/present.ML";
use "Thy/thm_deps.ML";

(*theorem database ML interface*)
use "Thy/thm_database.ML";

(*the Isar system*)
cd "Isar"; use "ROOT.ML"; cd "..";

use "axclass.ML";
use "codegen.ML";
use "Proof/extraction.ML";

(*old goal package -- obsolete*)
use "goals.ML";

(*the IsaPlanner subsystem*)
cd "IsaPlanner"; use "ROOT.ML"; cd "..";

cd "Tools"; use "ROOT.ML"; cd "..";

(*configuration for Proof General*)
setmp proofs 1 use "proof_general.ML";

use_thy "Pure"; structure Pure = struct val thy = theory "Pure" end;
use_thy "CPure"; structure CPure = struct val thy = theory "CPure" end;

(*final ML setup*)
use "install_pp.ML";
val use = ThyInfo.use;
val cd = File.cd o Path.unpack;
ml_prompts "ML> " "ML# ";

proofs := 0;
