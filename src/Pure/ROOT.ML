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
use "General/basics.ML";
use "library.ML";
cd "General"; use "ROOT.ML"; cd "..";

(*fundamental structures*)
use "name.ML";
use "term.ML";
use "term_subst.ML";
use "General/pretty.ML";
use "sorts.ML";
use "type.ML";
use "context.ML";
use "compress.ML";

(*inner syntax module*)
cd "Syntax"; use "ROOT.ML"; cd "..";
use "General/ml_syntax.ML";

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
use "morphism.ML";
use "variable.ML";
use "tctical.ML";
use "search.ML";
use "tactic.ML";
use "meta_simplifier.ML";
use "conjunction.ML";
use "assumption.ML";
use "goal.ML";

(*proof term operations*)
use "Proof/reconstruct.ML";
use "Proof/proof_syntax.ML";
use "Proof/proof_rewrite_rules.ML";
use "Proof/proofchecker.ML";

(*the main Isar system*)
cd "Isar"; use "ROOT.ML"; cd "..";
use "subgoal.ML";

use "Proof/extraction.ML";

cd "Tools"; use "ROOT.ML"; cd "..";

(*configuration for Proof General*)
cd "ProofGeneral"; use "ROOT.ML"; cd "..";

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
val cd = File.cd o Path.explode;
ml_prompts "ML> " "ML# ";

proofs := 0;
