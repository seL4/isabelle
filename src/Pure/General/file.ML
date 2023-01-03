(*  Title:      Pure/General/file.ML
    Author:     Makarius

File-system operations.
*)

signature FILE =
sig
  val standard_path: Path.T -> string
  val platform_path: Path.T -> string
  val bash_path: Path.T -> string
  val bash_paths: Path.T list -> string
  val bash_platform_path: Path.T -> string
  val symbolic_path: Path.T -> string
  val absolute_path: Path.T -> Path.T
  val full_path: Path.T -> Path.T -> Path.T
  val tmp_path: Path.T -> Path.T
  val exists: Path.T -> bool
  val rm: Path.T -> unit
  val is_dir: Path.T -> bool
  val is_file: Path.T -> bool
  val check_dir: Path.T -> Path.T
  val check_file: Path.T -> Path.T
  val fold_dir: (string -> 'a -> 'a) -> Path.T -> 'a -> 'a
  val read_dir: Path.T -> string list
  val read: Path.T -> string
  val read_lines: Path.T -> string list
  val write: Path.T -> string -> unit
  val append: Path.T -> string -> unit
  val write_list: Path.T -> string list -> unit
  val append_list: Path.T -> string list -> unit
  val eq: Path.T * Path.T -> bool
end;

structure File: FILE =
struct

(* system path representations *)

val standard_path = Path.implode o Path.expand;
val platform_path = ML_System.platform_path o standard_path;

val bash_path = Bash.string o standard_path;
val bash_paths = Bash.strings o map standard_path;

val bash_platform_path = Bash.string o platform_path;


(* symbolic path representation, e.g. "~~/src/Pure/ROOT.ML" *)

fun symbolic_path path =
  let
    val directories = rev (space_explode ":" (getenv "ISABELLE_DIRECTORIES"));
    val full_name = standard_path path;
    fun fold_path a =
      (case try (standard_path o Path.explode) a of
        SOME b =>
          if full_name = b then SOME a
          else
            (case try (unprefix (b ^ "/")) full_name of
              SOME name => SOME (a ^ "/" ^ name)
            | NONE => NONE)
      | NONE => NONE);
  in
    (case get_first fold_path directories of
      SOME name => name
    | NONE => Path.implode path)
  end;


(* full_path *)

val absolute_path =
  Path.expand #> (fn path =>
    if Path.is_absolute path then path
    else Path.explode (ML_System.standard_path (OS.FileSys.getDir ())) + path);

fun full_path dir path =
  let
    val path' = Path.expand path;
    val _ = Path.is_current path' andalso error "Bad file specification";
  in absolute_path (dir + path') end;


(* tmp_path *)

fun tmp_path path = Path.variable "ISABELLE_TMP" + Path.base path;


(* directory entries *)

val exists = can OS.FileSys.modTime o platform_path;

val rm = OS.FileSys.remove o platform_path;

fun test_dir path = the_default false (try OS.FileSys.isDir (platform_path path));
fun is_dir path = exists path andalso test_dir path;
fun is_file path = exists path andalso not (test_dir path);

fun check_dir path =
  if is_dir path then path
  else error ("No such directory: " ^ Path.print (Path.expand path));

fun check_file path =
  if is_file path then path
  else error ("No such file: " ^ Path.print (Path.expand path));


(* directory content *)

fun fold_dir f path a =
  check_dir path |> File_Stream.open_dir (fn stream =>
    let
      fun read x =
        (case OS.FileSys.readDir stream of
          NONE => x
        | SOME entry => read (f entry x));
    in read a end);

fun read_dir path = sort_strings (fold_dir cons path []);


(* read *)

val read = File_Stream.open_input File_Stream.input_all;

val read_lines = Bytes.read #> Bytes.trim_split_lines;


(* write *)

fun write_list path ss = File_Stream.open_output (fn stream => File_Stream.outputs stream ss) path;
fun append_list path ss = File_Stream.open_append (fn stream => File_Stream.outputs stream ss) path;

fun write path txt = write_list path [txt];
fun append path txt = append_list path [txt];


(* eq *)

fun eq paths =
  (case try (apply2 (OS.FileSys.fileId o platform_path)) paths of
    SOME ids => is_equal (OS.FileSys.compare ids)
  | NONE => false);

end;
