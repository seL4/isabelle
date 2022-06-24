(*  Title:      Pure/General/file_stream.ML
    Author:     Makarius

File-system stream operations.
*)

signature FILE_STREAM =
sig
  val open_dir: (OS.FileSys.dirstream -> 'a) -> Path.T -> 'a
  val open_input: (BinIO.instream -> 'a) -> Path.T -> 'a
  val open_output: (BinIO.outstream -> 'a) -> Path.T -> 'a
  val open_append: (BinIO.outstream -> 'a) -> Path.T -> 'a
  val input: BinIO.instream -> string
  val input_size: int -> BinIO.instream -> string
  val input_all: BinIO.instream -> string
  val output: BinIO.outstream -> string -> unit
  val outputs: BinIO.outstream -> string list -> unit
end;

structure File_Stream: FILE_STREAM =
struct

(* open streams *)

local

val platform_path = ML_System.platform_path o Path.implode o Path.expand;

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


(* input *)

val input = Byte.bytesToString o BinIO.input;
fun input_size n stream = Byte.bytesToString (BinIO.inputN (stream, n));
val input_all = Byte.bytesToString o BinIO.inputAll;


(* output *)

fun output file txt = BinIO.output (file, Byte.stringToBytes txt);
val outputs = List.app o output;

end;
