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

(* hide functors; saves space in PolyML *)
functor ThyScanFun() = struct end;
functor ThyParseFun() = struct end;

use "thy_syn.ML";
use "thy_read.ML";

structure ThySyn = ThySynFun(val user_keywords = [] and user_sections = []);
structure Readthy = ReadthyFUN(structure ThySyn = ThySyn);
open Readthy;

(* Do not hide ThySynFun and ReadthyFUN; they are still used *)

fun init_thy_reader () =
  use_string
   ["structure Readthy = ReadthyFUN(structure ThySyn = ThySyn);",
    "Readthy.loaded_thys := ! loaded_thys;",
    "open Readthy;"];

