(*  Title:      Pure/Thy/ROOT.ML
    ID:         $Id$
    Author:     Sonia Mahjoub and Tobias Nipkow and
                Markus Wenzel and Carsten Clasohm, TU Muenchen

This file builds the theory parser and autoloading system.
*)

use "thy_scan.ML";
use "thy_parse.ML";

structure ThyScan = ThyScanFun(Scanner);
structure ThyParse = ThyParseFun(structure Symtab = Symtab
  and ThyScan = ThyScan);

use "thy_syn.ML";
use "thm_database.ML";
use "thy_read.ML";

structure ThySyn = ThySynFun(val user_keywords = [] and user_sections = []);

(* hide functors; saves space in PolyML *)
functor ThyScanFun() = struct end;
functor ThyParseFun() = struct end;

fun init_thy_reader () =
  use_string
   ["structure ThmDB = \
    \ThmdbFUN(val ignore = [\"Trueprop\",\"all\",\"==>\",\"==\"]);",
    "structure Readthy = ReadthyFUN(structure ThySyn = ThySyn \
                                   \and ThmDB = ThmDB);",
    "open Readthy ThmDB;"];
