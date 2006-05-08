(*  Title:      Pure/ROOT.ML
    ID:         $Id$

Pure Isabelle.
*)

val banner = "Pure Isabelle";
val version = "Isabelle repository version";    (*filled in automatically!*)

(*if true then some tools will OMIT some proofs*)
val quick_and_dirty = ref false;

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
use "envir.ML";
use "logic.ML";
use "type_infer.ML";
use "consts.ML";
use "sign.ML";
use "pattern.ML";
use "unify.ML";
use "net.ML";
use "defs.ML";
use "theory.ML";
use "proofterm.ML";
use "thm.ML";
use "fact_index.ML";
use "pure_thy.ML";
use "display.ML";
use "drule.ML";
use "tctical.ML";
use "search.ML";
use "meta_simplifier.ML";
use "conjunction.ML";
use "goal.ML";
use "tactic.ML";

(*proof term operations*)
use "Proof/reconstruct.ML";
use "Proof/proof_syntax.ML";
use "Proof/proof_rewrite_rules.ML";
use "Proof/proofchecker.ML";

(*theory auto loader database*)
use "Thy/thy_load.ML";
use "Thy/thy_info.ML";

(*theory syntax*)
use "Isar/outer_lex.ML";

(*the Isar system*)
cd "Isar"; use "ROOT.ML"; cd "..";

use "Proof/extraction.ML";

(*the IsaPlanner subsystem*)
cd "IsaPlanner"; use "ROOT.ML"; cd "..";

cd "Tools"; use "ROOT.ML"; cd "..";

(*configuration for Proof General*)
(use |> setmp proofs 1 |> setmp quick_and_dirty true) "proof_general.ML";

use_thy "Pure";
structure Pure = struct val thy = theory "Pure" end;

Context.add_setup
 (Theory.del_modesyntax Syntax.default_mode Syntax.appl_syntax #>
  Theory.add_syntax Syntax.applC_syntax);
use_thy "CPure";
structure CPure = struct val thy = theory "CPure" end;

(*final ML setup*)
use "install_pp.ML";
val use = ThyInfo.use;
val cd = File.cd o Path.unpack;
ml_prompts "ML> " "ML# ";

proofs := 0;
