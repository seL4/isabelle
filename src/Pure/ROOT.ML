(*  Title:      Pure/ROOT.ML
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1993  University of Cambridge

Root file for Pure Isabelle.
*)

val banner = "Pure Isabelle";
val version = "Isabelle repository";

print_depth 1;
ml_prompts "> " "# ";


(*basic utils*)
use "library.ML";
use "table.ML";
use "object.ML";
use "seq.ML";
use "name_space.ML";
use "term.ML";

(*inner syntax module*)
cd "Syntax";
use "ROOT.ML";
cd "..";

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
use "thm.ML";
use "display.ML";
use "attribute.ML";
use "pure_thy.ML";
use "deriv.ML";
use "drule.ML";
use "tctical.ML";
use "search.ML";
use "tactic.ML";
use "goals.ML";
use "axclass.ML";

(*theory parser and loader*)
cd "Thy";
use "ROOT.ML";
cd "..";

use "install_pp.ML";

(*several object-logics declare theories named List or Option, hiding
  the eponymous basis library structures*)
structure BasisLibrary =
struct
  structure List = List and Option = Option;
end;

open Use;

print_depth 8;
