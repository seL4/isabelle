(*  Title:      Pure/General/file.ML
    ID:         $Id$
    Author:     Markus Wenzel, TU Muenchen

File system operations.
*)

signature FILE =
sig
  val sys_pack_fn: (Path.T -> string) ref
  val sys_unpack_fn: (string -> Path.T) ref
  val use: Path.T -> unit
  val rm: Path.T -> unit
  val cd: Path.T -> unit
  val pwd: unit -> Path.T
  val full_path: Path.T -> Path.T
  val tmp_path: Path.T -> Path.T
  val read: Path.T -> string
  val write: Path.T -> string -> unit
  val append: Path.T -> string -> unit
  val copy: Path.T -> Path.T -> unit
  eqtype info
  val info: Path.T -> info option
  val exists: Path.T -> bool
  val mkdir: Path.T -> unit
end;

structure File: FILE =
struct


(* system path representations (default: Unix) *)

val sys_pack_fn = ref Path.pack;
val sys_unpack_fn = ref Path.unpack;

fun sysify path = ! sys_pack_fn (Path.expand path);
fun unsysify s = ! sys_unpack_fn s;


val use = use o sysify;
val rm = OS.FileSys.remove o sysify;


(* current path *)

val cd = Library.cd o sysify;
val pwd = unsysify o Library.pwd;

fun full_path path =
  if Path.is_absolute path then path
  else Path.append (pwd ()) path;


(* tmp_path *)

fun tmp_path path =
  Path.append (Path.variable "ISABELLE_TMP") (Path.base path);


(* read / write files *)

fun fail_safe f g x =
  let val y = f x handle exn => (g x; raise exn)
  in g x; y end;


fun output txt stream = TextIO.output (stream, txt);

fun read path = fail_safe TextIO.inputAll TextIO.closeIn (TextIO.openIn (sysify path));
fun write path txt = fail_safe (output txt) TextIO.closeOut (TextIO.openOut (sysify path));
fun append path txt = fail_safe (output txt) TextIO.closeOut (TextIO.openAppend (sysify path));

fun copy inpath outpath = write outpath (read inpath);


(* file info *)

datatype info = Info of string;

fun info path =
  let val name = sysify path in
    (case file_info name of
      "" => None
    | s => Some (Info s))
  end;

val exists = is_some o info;


(* mkdir *)

fun mkdir path = (execute ("mkdir -p " ^ enclose "'" "'" (sysify path)); ());


end;
