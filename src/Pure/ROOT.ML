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
val version = "Isabelle-94 revision 7: November 96";

print_depth 1;

use "library.ML";
use "symtab.ML";
use "term.ML";

(*Syntax module*)
OS.FileSys.chDir "Syntax";
use "ROOT.ML";
OS.FileSys.chDir "..";

use "type.ML";
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

structure Pure  = struct val thy = Theory.pure_thy end;
structure CPure = struct val thy = Theory.cpure_thy end;

(*Theory parser and loader*)
OS.FileSys.chDir "Thy";
use "ROOT.ML";
OS.FileSys.chDir "..";

use "install_pp.ML";
fun init_database () = (init_thy_reader (); init_pps ());

