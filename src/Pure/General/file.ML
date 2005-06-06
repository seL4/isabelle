(*  Title:      Pure/General/file.ML
    ID:         $Id$
    Author:     Markus Wenzel, TU Muenchen

File system operations.
*)

signature FILE =
sig
  val unpack_platform_path_fn: (string -> Path.T) ref
  val unpack_platform_path: string -> Path.T
  val platform_path_fn: (Path.T -> string) ref
  val platform_path: Path.T -> string
  val shell_path_fn: (Path.T -> string) ref
  val shell_path: Path.T -> string
  val cd: Path.T -> unit
  val pwd: unit -> Path.T
  val full_path: Path.T -> Path.T
  val tmp_path: Path.T -> Path.T
  val isatool: string -> int
  val system_command: string -> unit
  val read: Path.T -> string
  val write: Path.T -> string -> unit
  val append: Path.T -> string -> unit
  val copy: Path.T -> Path.T -> unit
  val copy_dir: Path.T -> Path.T -> unit
  eqtype info
  val info: Path.T -> info option
  val exists: Path.T -> bool
  val rm: Path.T -> unit
  val mkdir: Path.T -> unit
  val use: Path.T -> unit
end;

structure File: FILE =
struct

(* platform specific path representations *)

val unpack_platform_path_fn = ref Path.unpack;
fun unpack_platform_path s = ! unpack_platform_path_fn s;

val platform_path_fn = ref (Path.pack o Path.expand);
fun platform_path path = ! platform_path_fn path;

val shell_path_fn = ref (enclose "'" "'" o Path.pack o Path.expand);
fun shell_path path = ! shell_path_fn path;


(* current path *)

val cd = Library.cd o platform_path;
val pwd = unpack_platform_path o Library.pwd;

fun norm_absolute p =
  let
    val p' = pwd ();
    fun norm p = if can cd p then pwd ()
      else Path.append (norm (Path.dir p)) (Path.base p);
    val p'' = norm p;
  in (cd p'; p'') end

fun full_path path =
  (if Path.is_absolute path then path
   else Path.append (pwd ()) path)
  |> norm_absolute;


(* tmp_path *)

fun tmp_path path =
  Path.append (Path.variable "ISABELLE_TMP") (Path.base path);


(* system commands *)

fun isatool cmd = system ("\"$ISATOOL\" " ^ cmd);

fun system_command cmd =
  if system cmd <> 0 then error ("System command failed: " ^ cmd)
  else ();


(* directory entries *)

datatype info = Info of string;

fun info path =
  Option.map (Info o Time.toString) (try OS.FileSys.modTime (platform_path path));

val exists = is_some o info;

val rm = OS.FileSys.remove o platform_path;

fun mkdir path = system_command ("mkdir -p " ^ shell_path path);

fun is_dir path =
  if_none (try OS.FileSys.isDir (platform_path path)) false;


(* read / write files *)

local

fun fail_safe f g x =
  let val y = f x handle exn => (g x; raise exn)
  in g x; y end;

fun output txt stream = TextIO.output (stream, txt);

in

fun read path =
  fail_safe TextIO.inputAll TextIO.closeIn (TextIO.openIn (platform_path path));

fun write path txt =
  fail_safe (output txt) TextIO.closeOut (TextIO.openOut (platform_path path));

fun append path txt =
  fail_safe (output txt) TextIO.closeOut (TextIO.openAppend (platform_path path));

end;

fun copy from to =
  let val target = if is_dir to then Path.append to (Path.base from) else to
  in write target (read from) end;

fun copy_dir from to =
  (system ("cp -r " ^ shell_path from ^ "/. " ^ shell_path to); ());  (* FIXME system_command *)


(* use ML files *)

val use = use o platform_path;

end;
