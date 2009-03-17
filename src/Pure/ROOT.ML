(*  Title:      Pure/ROOT.ML

Pure Isabelle.
*)

structure Distribution =     (*filled-in by makedist*)
struct
  val version = "Isabelle repository version";
  val is_official = false;
  val changelog = "";
end;

(*if true then some tools will OMIT some proofs*)
val quick_and_dirty = ref false;

print_depth 10;

(*basic tools*)
use "General/basics.ML";
use "library.ML";

cd "General"; use "ROOT.ML"; cd "..";
cd "Concurrent"; use "ROOT.ML"; cd "..";

(*fundamental structures*)
use "name.ML";
use "term.ML";
use "term_ord.ML";
use "term_subst.ML";
use "old_term.ML";
use "logic.ML";
use "General/pretty.ML";
use "context.ML";
use "context_position.ML";
use "Syntax/lexicon.ML";
use "Syntax/simple_syntax.ML";
use "sorts.ML";
use "type.ML";
use "config.ML";

(*inner syntax module*)
use "Syntax/ast.ML";
use "Syntax/syn_ext.ML";
use "Syntax/parser.ML";
use "Syntax/type_ext.ML";
use "Syntax/syn_trans.ML";
use "Syntax/mixfix.ML";
use "Syntax/printer.ML";
use "Syntax/syntax.ML";

use "type_infer.ML";
use "ML/ml_syntax.ML";

(*core of tactical proof system*)
use "net.ML";
use "item_net.ML";
use "envir.ML";
use "consts.ML";
use "primitive_defs.ML";
use "defs.ML";
use "sign.ML";
use "pattern.ML";
use "unify.ML";
use "theory.ML";
use "interpretation.ML";
use "proofterm.ML";
use "thm.ML";
use "more_thm.ML";
use "facts.ML";
use "pure_thy.ML";
use "display.ML";
use "drule.ML";
use "morphism.ML";
use "variable.ML";
use "conv.ML";
use "tctical.ML";
use "search.ML";
use "tactic.ML";
use "meta_simplifier.ML";
use "conjunction.ML";
use "assumption.ML";
use "goal.ML";
use "axclass.ML";

(*main Isar stuff*)
cd "Isar"; use "ROOT.ML"; cd "..";
use "subgoal.ML";

use "Proof/extraction.ML";

(*Isabelle/Isar system*)
use "System/session.ML";
use "System/isar.ML";
use "System/isabelle_process.ML";

(*additional tools*)
cd "Tools"; use "ROOT.ML"; cd "..";

use "codegen.ML";

(*configuration for Proof General*)
cd "ProofGeneral"; use "ROOT.ML"; cd "..";

use "pure_setup.ML";
