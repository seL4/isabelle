(*  Title:      Pure/Thy/ROOT.ML
    ID:         $Id$
    Author:     Sonia Mahjoub and Tobias Nipkow and
                Markus Wenzel and Carsten Clasohm, TU Muenchen

This file builds the theory parser and autoloading system.
*)

use "thy_scan.ML";
use "thy_parse.ML";
use "thy_syn.ML";
use "thm_database.ML";
use "symbol_input.ML";
use "thy_read.ML";

structure ThySyn = ThySynFun(val user_keywords = [] and user_sections = []);
structure ThmDB = ThmDBFun();
structure ReadThy = ReadthyFun(structure ThySyn = ThySyn and ThmDB = ThmDB);
open ThmDB ReadThy SymbolInput;


fun init_thy_reader () =
  use_string
   ["structure ThmDB = ThmDBFun();",
    "structure ReadThy = ReadthyFun(structure ThySyn = ThySyn \
                                   \and ThmDB = ThmDB);",
    "ReadThy.loaded_thys := !loaded_thys;",
    "map ReadThy.set_thy_reader_file (!thy_reader_files);",
    "ReadThy.base_path := !base_path;",
    "ReadThy.gif_path := !gif_path;",
    "ReadThy.index_path := !index_path;",
    "ReadThy.pure_subchart := !pure_subchart;",
    "ReadThy.make_html := !make_html;",
    "ThmDB.thm_db := !thm_db;",
    "open ThmDB ReadThy;",
    "read_thy_reader_files ();"];


(* FIXME tmp *)

fun set_session s =
  writeln ("This is the " ^ quote s ^ " session.");
