(*  Title:      Pure/ROOT.ML
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1993  University of Cambridge

Root file for Pure Isabelle: all modules in proper order for loading.
Loads pure Isabelle into an empty database (see also Makefile).

TO DO:
instantiation of theorems can lead to inconsistent sorting of type vars if
'a::S is already present and 'a::T is introduced.
*)

val banner = "Pure Isabelle";
val version = "Isabelle-94 revision 8: May 1997";

print_depth 1;

use "library.ML";
use "symtab.ML";
use "name_space.ML";
use "term.ML";

(*Syntax module*)
cd "Syntax";
use "ROOT.ML";
cd "..";

use "sorts.ML";
use "type_infer.ML";
use "type.ML";
use "data.ML";
use "sign.ML";
use "sequence.ML";
use "envir.ML";
use "pattern.ML";
use "unify.ML";
use "net.ML";
use "logic.ML";
use "theory.ML";
use "thm.ML";
use "deriv.ML";
use "display.ML";
use "drule.ML";
use "tctical.ML";
use "search.ML";
use "tactic.ML";
use "goals.ML";
use "axclass.ML";

structure Pure  = struct val thy = Theory.pure end;
structure CPure = struct val thy = Theory.cpure end;

(*Theory parser and loader*)
cd "Thy";
use "ROOT.ML";
cd "..";

use "install_pp.ML";

print_depth 8;
