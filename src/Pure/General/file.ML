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
  val absolute_path: Path.T -> Path.T
  val full_path: Path.T -> Path.T -> Path.T
  val tmp_path: Path.T -> Path.T
  val exists: Path.T -> bool
  val rm: Path.T -> unit
  val is_dir: Path.T -> bool
  val is_file: Path.T -> bool
  val check_dir: Path.T -> Path.T
  val check_file: Path.T -> Path.T
  val open_dir: (OS.FileSys.dirstream -> 'a) -> Path.T -> 'a
  val open_input: (BinIO.instream -> 'a) -> Path.T -> 'a
  val open_output: (BinIO.outstream -> 'a) -> Path.T -> 'a
  val open_append: (BinIO.outstream -> 'a) -> Path.T -> 'a
  val fold_dir: (string -> 'a -> 'a) -> Path.T -> 'a -> 'a
  val read_dir: Path.T -> string list
  val fold_lines: (string -> 'a -> 'a) -> Path.T -> 'a -> 'a
  val fold_pages: (string -> 'a -> 'a) -> Path.T -> 'a -> 'a
  val read_lines: Path.T -> string list
  val read_pages: Path.T -> string list
  val read: Path.T -> string
  val write: Path.T -> string -> unit
  val append: Path.T -> string -> unit
  val generate: Path.T -> string -> unit
  val output: BinIO.outstream -> string -> unit
  val write_list: Path.T -> string list -> unit
  val append_list: Path.T -> string list -> unit
  val write_buffer: Path.T -> Buffer.T -> unit
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


(* open streams *)

local

fun with_file open_file close_file f =
  Thread_Attributes.uninterruptible (fn restore_attributes => fn path =>
    let
      val file = open_file path;
      val result = Exn.capture (restore_attributes f) file;
    in close_file file; Exn.release result end);

in

fun open_dir f = with_file OS.FileSys.openDir OS.FileSys.closeDir f o platform_path;
fun open_input f = with_file BinIO.openIn BinIO.closeIn f o platform_path;
fun open_output f = with_file BinIO.openOut BinIO.closeOut f o platform_path;
fun open_append f = with_file BinIO.openAppend BinIO.closeOut f o platform_path;

end;


(* directory content *)

fun fold_dir f path a =
  check_dir path |> open_dir (fn stream =>
    let
      fun read x =
        (case OS.FileSys.readDir stream of
          NONE => x
        | SOME entry => read (f entry x));
    in read a end);

fun read_dir path = sort_strings (fold_dir cons path []);


(* input *)

(*
  scalable iterator:
  . avoid size limit of TextIO.inputAll and overhead of many TextIO.inputLine
  . optional terminator at end-of-input
*)
fun fold_chunks terminator f path a = open_input (fn file =>
  let
    fun read buf x =
      (case Byte.bytesToString (BinIO.input file) of
        "" => (case Buffer.content buf of "" => x | line => f line x)
      | input =>
          (case String.fields (fn c => c = terminator) input of
            [rest] => read (Buffer.add rest buf) x
          | line :: more => read_lines more (f (Buffer.content (Buffer.add line buf)) x)))
    and read_lines [rest] x = read (Buffer.add rest Buffer.empty) x
      | read_lines (line :: more) x = read_lines more (f line x);
  in read Buffer.empty a end) path;

fun fold_lines f = fold_chunks #"\n" f;
fun fold_pages f = fold_chunks #"\f" f;

fun read_lines path = rev (fold_lines cons path []);
fun read_pages path = rev (fold_pages cons path []);

val read = open_input (Byte.bytesToString o BinIO.inputAll);


(* output *)

fun output file txt = BinIO.output (file, Byte.stringToBytes txt);

fun output_list txts file = List.app (output file) txts;
fun write_list path txts = open_output (output_list txts) path;
fun append_list path txts = open_append (output_list txts) path;

fun write path txt = write_list path [txt];
fun append path txt = append_list path [txt];
fun generate path txt = if try read path = SOME txt then () else write path txt;

fun write_buffer path buf = open_output (Buffer.output buf o output) path;


(* eq *)

fun eq paths =
  (case try (apply2 (OS.FileSys.fileId o platform_path)) paths of
    SOME ids => is_equal (OS.FileSys.compare ids)
  | NONE => false);

end;
