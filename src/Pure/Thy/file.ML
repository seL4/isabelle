(*  Title:      Pure/Thy/file.ML
    ID:         $Id$
    Author:     Markus Wenzel, TU Muenchen

File system operations.
*)

signature BASIC_FILE =
sig
  val maketest: string -> unit
end;

signature FILE =
sig
  include BASIC_FILE
  val exists: string -> bool
  val read: string -> string
  val write: string -> string -> unit
  val append: string -> string -> unit
  val copy: string -> string -> unit
end;

structure File: FILE =
struct


(* exists *)

fun exists name = (file_info name <> "");


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

fun copy infile outfile =               (* FIXME improve *)
  if not (exists infile) then error ("File not found: " ^ quote infile)
  else write outfile (read infile);


(*for the "test" target in IsaMakefiles -- signifies successful termination*)
fun maketest msg =
  (writeln msg; write "test" "Test examples ran successfully\n");


end;


structure BasicFile: BASIC_FILE = File;
open BasicFile;
