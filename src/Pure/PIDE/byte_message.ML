(*  Title:      Pure/General/byte_message.ML
    Author:     Makarius

Byte-oriented messages.
*)

signature BYTE_MESSAGE =
sig
  val write: BinIO.outstream -> string -> unit
  val newline: BinIO.outstream -> unit
  val flush: BinIO.outstream -> unit
  val read: BinIO.instream -> int -> string
  val read_block: BinIO.instream -> int -> string option
  val read_line: BinIO.instream -> string option

  val write_header: BinIO.outstream -> int list -> unit
  val read_header: BinIO.instream -> int list option
  val read_header1: BinIO.instream -> int option

  val write_message: BinIO.outstream -> string list -> unit
  val read_message: BinIO.instream -> string list option

  val write_line_message: BinIO.outstream -> string -> unit
  val read_line_message: BinIO.instream -> string option
end;

structure Byte_Message: BYTE_MESSAGE =
struct

(* output operations *)

fun write stream s = BinIO.output (stream, Byte.stringToBytes s);

fun newline stream = write stream "\n";

fun flush stream = ignore (try BinIO.flushOut stream);


(* input operations *)

fun read stream n = Byte.bytesToString (BinIO.inputN (stream, n));

fun read_block stream n =
  let val msg = read stream n
  in if size msg = n then SOME msg else NONE end;

fun read_line stream =
  let
    val result = trim_line o String.implode o rev;
    fun read cs =
      (case BinIO.input1 stream of
        NONE => if null cs then NONE else SOME (result cs)
      | SOME b =>
          (case Byte.byteToChar b of
            #"\n" => SOME (result cs)
          | c => read (c :: cs)));
  in read [] end;


(* header with chunk lengths *)

fun write_header stream ns =
 (write stream (space_implode "," (map string_of_int ns));
  newline stream);

fun err_header line = error ("Malformed message header: " ^ quote line)

fun parse_header line =
  map Value.parse_nat (space_explode "," line)
    handle Fail _ => err_header line

fun read_header stream =
  read_line stream |> Option.map parse_header;

fun read_header1 stream =
  read_line stream |> Option.map (fn line =>
    (case parse_header line of
      [n] => n
    | _ => err_header line));


(* messages with multiple chunks (arbitrary content) *)

fun write_message stream chunks =
 (write_header stream (map size chunks);
  List.app (write stream) chunks;
  flush stream);

fun read_chunk stream n =
  let
    val chunk = read stream n;
    val len = size chunk;
  in
    if len = n then chunk
    else
      error ("Malformed message chunk: unexpected EOF after " ^
        string_of_int len ^ " of " ^ string_of_int n ^ " bytes")
  end;

fun read_message stream =
  read_header stream |> (Option.map o map) (read_chunk stream);


(* hybrid messages: line or length+block (with content restriction) *)

fun is_length s =
  s <> "" andalso forall_string Symbol.is_ascii_digit s;

fun has_line_terminator s =
  String.isSuffix "\r" s orelse String.isSuffix "\n" s;

fun write_line_message stream msg =
  if is_length msg orelse has_line_terminator msg then
    error ("Bad content for line message:\n" ^ implode (take 100 (Symbol.explode msg)))
  else
    let val n = size msg in
      if n > 100 orelse exists_string (fn s => s = "\n") msg then
        write_header stream [n + 1]
      else ();
      write stream msg;
      newline stream;
      flush stream
    end;

fun read_line_message stream =
  (case read_line stream of
    SOME line =>
      (case try Value.parse_nat line of
        NONE => SOME line
      | SOME n => Option.map trim_line (read_block stream n))
  | NONE => NONE) handle IO.Io _ => NONE;

end;
