(*  Title:      Pure/Thy/ROOT.ML
    ID:         $Id$
    Author:     Sonia Mahjoub and Tobias Nipkow and
                Markus Wenzel and Carsten Clasohm, TU Muenchen

This file builds the theory parser and autoloading system.
*)

use "thy_scan.ML";
use "thy_parse.ML";
use "thy_syn.ML";
use "thy_info.ML";
use "browser_info.ML";
use "thm_database.ML";
use "symbol_input.ML";
use "thy_read.ML";

open ThmDB ReadThy ThyInfo BrowserInfo SymbolInput;

structure ThySyn = ThySynFun(val user_keywords = [] and user_sections = []);
set_parser ThySyn.parse;

(* FIXME tmp *)

fun set_session s =
  writeln ("This is the " ^ quote s ^ " session.");
