(*  Title:      Pure/Thy/file.ML
    ID:         $Id$
    Author:     Markus Wenzel, TU Muenchen

File system operations.
*)

signature FILE =
sig
  val tmp_name: string -> string
  val exists: string -> bool
  val info: string -> string
  val read: string -> string
  val write: string -> string -> unit
  val append: string -> string -> unit
  val copy: string -> string -> unit
  val source: string -> (string, string list) Source.source
end;

structure File: FILE =
struct


(* tmp_name *)

fun tmp_name name =
  Path.pack (Path.evaluate (Path.unpack o getenv)
    (Path.append (Path.variable "ISABELLE_TMP") (Path.unpack name)));


(* exists / info *)

fun exists name = (file_info name <> "");
val info = file_info;


(* read / write files *)

fun read name =
  let
    val instream  = TextIO.openIn name;
    val intext = TextIO.inputAll instream;
  in
    TextIO.closeIn instream;
    intext
  end;

fun write name txt =
  let val outstream = TextIO.openOut name in
    TextIO.output (outstream, txt);
    TextIO.closeOut outstream
  end;

fun append name txt =
  let val outstream = TextIO.openAppend name in
    TextIO.output (outstream, txt);
    TextIO.closeOut outstream
  end;

fun copy infile outfile =
  if not (exists infile) then error ("File not found: " ^ quote infile)
  else write outfile (read infile);

val source = Source.of_string o read;


end;
