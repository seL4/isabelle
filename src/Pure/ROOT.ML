(*  Title:      Pure/ROOT.ML
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1993  University of Cambridge

Root file for Pure Isabelle.
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

(*inner syntax module*)
cd "Syntax"; use "ROOT.ML"; cd "..";

(*core system*)
use "type_infer.ML";
use "sign.ML";
use "envir.ML";
use "pattern.ML";
use "unify.ML";
use "net.ML";
use "logic.ML";
use "theory.ML";
use "theory_data.ML";
use "context.ML";
use "proofterm.ML";
use "thm.ML";
use "display.ML";
use "fact_index.ML";
use "pure_thy.ML";
use "drule.ML";
use "meta_simplifier.ML";
use "tctical.ML";
use "search.ML";
use "tactic.ML";

(*proof term operations*)
cd "Proof"; use "ROOT.ML"; cd "..";

(*theory system operations*)
cd "Thy"; use "ROOT.ML"; cd "..";

(*the Isar subsystem*)
cd "Isar"; use "ROOT.ML"; cd "..";

use "axclass.ML";
use "codegen.ML";
use "Proof/extraction.ML";

(*old-style goal package*)
use "goals.ML";

(*configuration for Proof General*)
use "proof_general.ML";

(*final Pure theory setup*)
use "pure.ML";

(*several object-logics declare theories that hide basis library structures*)
structure BasisLibrary =
struct
  structure List = List;
  structure Option = Option;
  structure Bool = Bool;
  structure String = String;
  structure Int = Int;
  structure Real = Real;
end;

use "install_pp.ML";

val use = ThyInfo.use;
val cd = File.cd o Path.unpack;

ml_prompts "ML> " "ML# ";

proofs := 0;
