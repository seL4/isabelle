(*  Title:      Pure/General/file.ML
    ID:         $Id$
    Author:     Markus Wenzel, TU Muenchen

File system operations.
*)

signature FILE =
sig
  val sys_pack_fn: (Path.T -> string) ref
  val sys_unpack_fn: (string -> Path.T) ref
  val sysify_path: Path.T -> string
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
  val copy_all: Path.T -> Path.T -> unit
  val plain_use: Path.T -> unit
  val symbol_use: Path.T -> unit
end;

structure File: FILE =
struct


(* system path representations (default: Unix) *)

val sys_pack_fn = ref Path.pack;
val sys_unpack_fn = ref Path.unpack;

fun sysify_path path = ! sys_pack_fn (Path.expand path);
fun unsysify_path s = ! sys_unpack_fn s;

val rm = OS.FileSys.remove o sysify_path;


(* current path *)

val cd = Library.cd o sysify_path;
val pwd = unsysify_path o Library.pwd;

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

fun read path = fail_safe TextIO.inputAll TextIO.closeIn (TextIO.openIn (sysify_path path));
fun write path txt = fail_safe (output txt) TextIO.closeOut (TextIO.openOut (sysify_path path));
fun append path txt =
  fail_safe (output txt) TextIO.closeOut (TextIO.openAppend (sysify_path path));

fun copy inpath outpath = write outpath (read inpath);


(* file info *)

datatype info = Info of string;

fun info path =
  let val name = sysify_path path in
    (case file_info name of
      "" => None
    | s => Some (Info s))
  end;

val exists = is_some o info;


(* directories *)

val quote_sysify = enclose "'" "'" o sysify_path;

fun system_command cmd =
  if system cmd <> 0 then error ("System command failed: " ^ cmd)
  else ();
    
fun mkdir path = system_command ("mkdir -p " ^ quote_sysify path);

fun copy_all path1 path2 =  (*dereferences symlinks!*)
  system_command ("cp -r " ^ quote_sysify path1 ^ " " ^ quote_sysify path2);


(* symbol_use *)

val plain_use = use o sysify_path;

(* version of 'use' with input filtering *)

val symbol_use =
  if not needs_filtered_use then plain_use	(*ML system (wrongly!) accepts non-ASCII*)
  else
    fn path =>
      let
        val txt = read path;
        val txt_out = Symbol.input txt;
      in
        if txt = txt_out then plain_use path
        else
          let val tmp_path = tmp_path path in
            write tmp_path txt_out;
            plain_use tmp_path handle exn => (rm tmp_path; raise exn);
            rm tmp_path
          end
      end;

end;
