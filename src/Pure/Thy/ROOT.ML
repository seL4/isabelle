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
use "thy_read.ML";

structure ThySyn = ThySynFun(val user_keywords = [] and user_sections = []);
structure Readthy = ReadthyFUN(structure ThySyn = ThySyn);
open Readthy;

fun init_thy_reader () =
  use_string
   ["structure Readthy = ReadthyFUN(structure ThySyn = ThySyn);",
    "Readthy.loaded_thys := ! loaded_thys;",
    "open Readthy;"];

