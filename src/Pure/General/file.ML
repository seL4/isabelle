(*  Title:      Pure/General/file.ML
    ID:         $Id$
    Author:     Markus Wenzel, TU Muenchen

File system operations.

TODO:
  - close in case of error (!?);
*)

signature FILE =
sig
  val sys_path_fn: (Path.T -> string) ref
  val tmp_path: Path.T -> Path.T
  eqtype info
  val info: Path.T -> info option
  val join_info: info -> info -> info
  val exists: Path.T -> bool
  val read: Path.T -> string
  val write: Path.T -> string -> unit
  val append: Path.T -> string -> unit
  val copy: Path.T -> Path.T -> unit
  val use: Path.T -> unit
  val cd: Path.T -> unit
  val rm: Path.T -> unit
end;

structure File: FILE =
struct


(* sys_path (default for Unix) *)

val sys_path_fn = ref Path.pack;
fun sysify path = ! sys_path_fn (Path.expand path);


(* tmp_path *)

fun tmp_path path =
  Path.append (Path.variable "ISABELLE_TMP") (Path.base path);


(* info / exists *)

datatype info = Info of string list;

fun join_info (Info xs) (Info ys) = Info (xs @ ys);

fun info path =
  let val name = sysify path in
    (case file_info name of
      "" => None
    | s => Some (Info [name ^ ": " ^ s]))	(* FIXME include full path (!?) *)
  end;

val exists = is_some o info;


(* read / write files *)

fun read path =
  let
    val instream  = TextIO.openIn (sysify path);
    val intext = TextIO.inputAll instream;
  in
    TextIO.closeIn instream;
    intext
  end;

fun write path txt =
  let val outstream = TextIO.openOut (sysify path) in
    TextIO.output (outstream, txt);
    TextIO.closeOut outstream
  end;

fun append path txt =
  let val outstream = TextIO.openAppend (sysify path) in
    TextIO.output (outstream, txt);
    TextIO.closeOut outstream
  end;

fun copy inpath outpath = write outpath (read inpath);


(* misc operations *)

val use = use o sysify;
val cd = Library.cd o sysify;
val rm = OS.FileSys.remove o sysify;


end;
