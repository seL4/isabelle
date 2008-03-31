(*  Title:      Pure/General/file.ML
    ID:         $Id$
    Author:     Markus Wenzel, TU Muenchen

File system operations.
*)

signature FILE =
sig
  val platform_path: Path.T -> string
  val shell_path: Path.T -> string
  val cd: Path.T -> unit
  val pwd: unit -> Path.T
  val full_path: Path.T -> Path.T
  val tmp_path: Path.T -> Path.T
  val isatool: string -> int
  val system_command: string -> unit
  eqtype ident
  val rep_ident: ident -> string
  val ident: Path.T -> ident option
  val exists: Path.T -> bool
  val check: Path.T -> unit
  val rm: Path.T -> unit
  val mkdir: Path.T -> unit
  val open_input: (TextIO.instream -> 'a) -> Path.T -> 'a
  val open_output: (TextIO.outstream -> 'a) -> Path.T -> 'a
  val open_append: (TextIO.outstream -> 'a) -> Path.T -> 'a
  val read: Path.T -> string
  val write: Path.T -> string -> unit
  val append: Path.T -> string -> unit
  val write_list: Path.T -> string list -> unit
  val append_list: Path.T -> string list -> unit
  val eq: Path.T * Path.T -> bool
  val copy: Path.T -> Path.T -> unit
  val copy_dir: Path.T -> Path.T -> unit
end;

structure File: FILE =
struct

(* system path representations *)

val platform_path = Path.implode o Path.expand;
val shell_path = enclose "'" "'" o Path.implode o Path.expand;


(* current working directory *)

val cd = cd o platform_path;
val pwd = Path.explode o pwd;

(* FIXME not thread-safe! *)
fun norm_absolute p =
  let
    val p' = pwd ();
    fun norm p = if can cd p then pwd ()
      else Path.append (norm (Path.dir p)) (Path.base p);
    val p'' = norm p;
  in (cd p'; p'') end;

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

datatype ident = Ident of string;

fun rep_ident (Ident s) = s;

fun ident path =
  (case try OS.FileSys.modTime (platform_path path) of
    NONE => NONE
  | SOME time => SOME (Ident
      (case getenv "ISABELLE_FILE_IDENT" of
        "" => Path.implode (full_path path) ^ ": " ^ Time.toString time
      | cmd =>
         let
           val (id, rc) = system_out ("\"$ISABELLE_HOME/lib/scripts/fileident\" " ^ shell_path path)
         in
           if id <> "" andalso rc = 0 then id
           else error ("Failed to identify file " ^ quote (Path.implode path) ^ " by " ^ cmd)
         end)));

val exists = can OS.FileSys.modTime o platform_path;

fun check path =
  if exists path then ()
  else error ("No such file or directory: " ^ quote (Path.implode path));

val rm = OS.FileSys.remove o platform_path;

fun mkdir path = system_command ("mkdir -p " ^ shell_path path);

fun is_dir path =
  the_default false (try OS.FileSys.isDir (platform_path path));


(* read / write files *)

local

fun with_file open_file close_file f path =
  let val file = open_file path
  in Exn.release (Exn.capture f file before close_file file) end;

fun output txts file = List.app (fn txt => TextIO.output (file, txt)) txts;

in

fun open_input f = with_file TextIO.openIn TextIO.closeIn f o platform_path;
fun open_output f = with_file TextIO.openOut TextIO.closeOut f o platform_path;
fun open_append f = with_file TextIO.openAppend TextIO.closeOut f o platform_path;

val read = open_input TextIO.inputAll;

fun write_list path txts = open_output (output txts) path;
fun append_list path txts = open_append (output txts) path;

fun write path txt = write_list path [txt];
fun append path txt = append_list path [txt];

end;

fun eq paths =
  (case try (pairself (OS.FileSys.fileId o platform_path)) paths of
    SOME ids => OS.FileSys.compare ids = EQUAL
  | NONE => false);

fun copy src dst =
  if eq (src, dst) then ()
  else
    let val target = if is_dir dst then Path.append dst (Path.base src) else dst
    in write target (read src) end;

fun copy_dir src dst =
  if eq (src, dst) then ()
  else (system_command ("cp -r -f " ^ shell_path src ^ "/. " ^ shell_path dst); ());

end;
