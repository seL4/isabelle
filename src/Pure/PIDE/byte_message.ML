(*  Title:      Pure/PIDE/byte_message.ML
    Author:     Makarius

Byte-oriented messages.
*)

signature BYTE_MESSAGE =
sig
  val write: BinIO.outstream -> Bytes.T list -> unit
  val write_yxml: BinIO.outstream -> XML.tree -> unit
  val flush: BinIO.outstream -> unit
  val write_line: BinIO.outstream -> Bytes.T -> unit
  val read: BinIO.instream -> int -> Bytes.T
  val read_block: BinIO.instream -> int -> Bytes.T option * int
  val read_line: BinIO.instream -> Bytes.T option
  val write_message: BinIO.outstream -> Bytes.T list -> unit
  val write_message_string: BinIO.outstream -> string list -> unit
  val write_message_yxml: BinIO.outstream -> XML.body list -> unit
  val read_message: BinIO.instream -> Bytes.T list option
  val read_message_string: BinIO.instream -> string list option
  val write_line_message: BinIO.outstream -> Bytes.T -> unit
  val read_line_message: BinIO.instream -> Bytes.T option
end;

structure Byte_Message: BYTE_MESSAGE =
struct

(* output operations *)

val write = List.app o Bytes.write_stream;

fun write_yxml stream tree =
  YXML.traverse (fn s => fn () => File_Stream.output stream s) tree ();

fun flush stream = ignore (try BinIO.flushOut stream);

fun write_line stream bs = (write stream [bs, Bytes.newline]; flush stream);


(* input operations *)

fun read stream n = Bytes.read_stream n stream;

fun read_block stream n =
  let
    val msg = read stream n;
    val len = Bytes.size msg;
  in (if len = n then SOME msg else NONE, len) end;

fun read_line stream =
  let
    val result = SOME o Bytes.trim_line;
    fun read_body bs =
      (case BinIO.input1 stream of
        NONE => if Bytes.is_empty bs then NONE else result bs
      | SOME b =>
          (case Byte.byteToChar b of
            #"\n" => result bs
          | c => read_body (Bytes.add (str c) bs)));
  in read_body Bytes.empty end;


(* messages with multiple chunks (arbitrary content) *)

fun make_header ns =
  [Bytes.string (space_implode "," (map Value.print_int ns)), Bytes.newline];

fun write_message stream chunks =
  (write stream (make_header (map Bytes.size chunks) @ chunks); flush stream);

fun write_message_string stream =
  write_message stream o map Bytes.string;

fun write_message_yxml stream chunks =
  (write stream (make_header (map YXML.body_size chunks));
   (List.app o List.app) (write_yxml stream) chunks;
   flush stream);

fun parse_header line =
  map Value.parse_nat (space_explode "," line)
    handle Fail _ => error ("Malformed message header: " ^ quote line);

fun read_chunk stream n =
  (case read_block stream n of
    (SOME chunk, _) => chunk
  | (NONE, len) =>
      error ("Malformed message chunk: unexpected EOF after " ^
        string_of_int len ^ " of " ^ string_of_int n ^ " bytes"));

fun read_message stream =
  read_line stream |> Option.map (Bytes.content #> parse_header #> map (read_chunk stream));

fun read_message_string stream =
  read_message stream |> (Option.map o map) Bytes.content;


(* hybrid messages: line or length+block (with content restriction) *)

(* line message format *)

fun is_length msg =
  not (Bytes.is_empty msg) andalso Bytes.forall_string Symbol.is_ascii_digit msg;

fun is_terminated msg =
  (case Bytes.last_string msg of
    NONE => false
  | SOME s => Symbol.is_ascii_line_terminator s);

fun write_line_message stream msg =
  if is_length msg orelse is_terminated msg then
    error ("Bad content for line message:\n" ^ Bytes.beginning 100 msg)
  else
    let val n = Bytes.size msg in
      write stream
        ((if n > 100 orelse Bytes.exists_string (fn s => s = "\n") msg
          then make_header [n + 1] else []) @ [msg, Bytes.newline]);
      flush stream
    end;

fun read_line_message stream =
  (case read_line stream of
    NONE => NONE
  | SOME line =>
      (case try (Value.parse_nat o Bytes.content) line of
        NONE => SOME line
      | SOME n => Option.map Bytes.trim_line (#1 (read_block stream n))));

end;
