(*  Title:      Pure/Thy/ROOT.ML
    ID:         $Id$
    Author:     Sonia Mahjoub and Tobias Nipkow and
                Markus Wenzel and Carsten Clasohm, TU Muenchen

This file builds the theory parser and autoloading system.
*)

(* FIXME remove (still needed by HOL/Datatype.ML) *)
use "scan.ML"; use "parse.ML";

use "thy_scan.ML";
use "thy_parse.ML";
use "thy_read.ML";

structure ThyScan = ThyScanFun(Scanner);
structure ThyParse = ThyParseFun(structure Symtab = Symtab
  and ThyScan = ThyScan);
structure ThyRead = ThyReadFun(structure ThyParse = ThyParse);
open ThyRead;


(* FIXME tmp hack *)

fun eval txt =
  let
    val tmp_name = "/tmp/.eval.tmp";
    val tmp_file = open_out tmp_name;
  in
    output (tmp_file, txt);
    close_out tmp_file;
    use tmp_name;
    delete_file tmp_name
  end;


fun init_thy_reader () = 
  eval   (* FIXME use_string *)
    "structure ThyRead = ThyReadFun(structure ThyParse = ThyParse);\n\
    \ThyRead.loaded_thys := ! loaded_thys;\n\
    \open ThyRead;\n";

