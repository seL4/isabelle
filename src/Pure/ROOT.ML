(*  Title:      Pure/ROOT.ML
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1993  University of Cambridge

Root file for Pure Isabelle.
*)

val banner = "Pure Isabelle";
val version = "Isabelle repository";

print_depth 1;

(*global flags*)
val print_mode = ref ([]: string list);
val quick_and_dirty = ref false;        (*if true then some packages will OMIT SOME PROOFS*)

(*fake hiding of private structures*)
structure Hidden = struct end;

(*basic tools*)
use "library.ML";
cd "General"; use "ROOT.ML"; cd "..";
use "term.ML";

(*inner syntax module*)
cd "Syntax"; use "ROOT.ML"; cd "..";

(*main system*)
use "sorts.ML";
use "type_infer.ML";
use "type.ML";
use "sign.ML";
use "envir.ML";
use "pattern.ML";
use "unify.ML";
use "net.ML";
use "logic.ML";
use "theory.ML";
use "theory_data.ML";
use "context.ML";
use "object_logic.ML";
use "thm.ML";
use "display.ML";
use "pure_thy.ML";
use "deriv.ML";
use "drule.ML";
use "locale.ML";
use "tctical.ML";
use "search.ML";
use "tactic.ML";
use "goals.ML";

(*theory system operations*)
cd "Thy"; use "ROOT.ML"; cd "..";

(*the Isar subsystem*)
cd "Isar"; use "ROOT.ML"; cd "..";

(*final Pure theory setup*)
use "axclass.ML";
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

print_depth 8;
(*ml_prompts "ML> " "ML# ";*)

Session.finish ();
