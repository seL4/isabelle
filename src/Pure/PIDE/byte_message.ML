(*  Title:      Pure/General/byte_message.ML
    Author:     Makarius

Byte-oriented messages.
*)

signature BYTE_MESSAGE =
sig
  val write: BinIO.outstream -> string -> unit
  val flush: BinIO.outstream -> unit

  val read: BinIO.instream -> int -> string
  val read_block: BinIO.instream -> int -> string option * int
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
  let
    val msg = read stream n;
    val len = size msg;
  in (if len = n then SOME msg else NONE, len) end;

fun read_line stream =
  let
    val result = trim_line o String.implode o rev;
    fun read_body cs =
      (case BinIO.input1 stream of
        NONE => if null cs then NONE else SOME (result cs)
      | SOME b =>
          (case Byte.byteToChar b of
            #"\n" => SOME (result cs)
          | c => read_body (c :: cs)));
  in read_body [] end;


(* header with chunk lengths *)

fun write_header stream ns =
 (write stream (space_implode "," (map string_of_int ns));
  newline stream);

fun err_header line =
  error ("Malformed message header: " ^ quote line);

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
  (case read_block stream n of
    (SOME chunk, _) => chunk
  | (NONE, len) =>
      error ("Malformed message chunk: unexpected EOF after " ^
        string_of_int len ^ " of " ^ string_of_int n ^ " bytes"));

fun read_message stream =
  read_header stream |> (Option.map o map) (read_chunk stream);


(* hybrid messages: line or length+block (with content restriction) *)

fun is_length msg =
  msg <> "" andalso forall_string Symbol.is_ascii_digit msg;

fun is_terminated msg =
  let val len = size msg
  in len > 0 andalso Symbol.is_ascii_line_terminator (str (String.sub (msg, len - 1))) end;

fun write_line_message stream msg =
  if is_length msg orelse is_terminated msg then
    error ("Bad content for line message:\n" ^ implode (take 100 (Symbol.explode msg)))
  else
    let val n = size msg in
      if n > 100 orelse exists_string (fn s => s = "\n") msg then write_header stream [n + 1]
      else ();
      write stream msg;
      newline stream;
      flush stream
    end;

fun read_line_message stream =
  (case read_line stream of
    NONE => NONE
  | SOME line =>
      (case try Value.parse_nat line of
        NONE => SOME line
      | SOME n => Option.map trim_line (#1 (read_block stream n))));

end;
