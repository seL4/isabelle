(*  Title:      Pure/General/byte_message.ML
    Author:     Makarius

Byte-oriented messages.
*)

signature BYTE_MESSAGE =
sig
  val write: BinIO.outstream -> string list -> unit
  val write_yxml: BinIO.outstream -> XML.tree -> unit
  val flush: BinIO.outstream -> unit
  val write_line: BinIO.outstream -> string -> unit
  val read: BinIO.instream -> int -> string
  val read_block: BinIO.instream -> int -> string option * int
  val read_line: BinIO.instream -> string option
  val write_message: BinIO.outstream -> string list -> unit
  val write_message_yxml: BinIO.outstream -> XML.body list -> unit
  val read_message: BinIO.instream -> string list option
  val write_line_message: BinIO.outstream -> string -> unit
  val read_line_message: BinIO.instream -> string option
end;

structure Byte_Message: BYTE_MESSAGE =
struct

(* output operations *)

fun write stream = List.app (File.output stream);

fun write_yxml stream tree = YXML.traverse (fn s => fn () => File.output stream s) tree ();

fun flush stream = ignore (try BinIO.flushOut stream);

fun write_line stream s = (write stream [s, "\n"]; flush stream);


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


(* messages with multiple chunks (arbitrary content) *)

fun make_header ns =
  [space_implode "," (map Value.print_int ns), "\n"];

fun write_message stream chunks =
  (write stream (make_header (map size chunks) @ chunks); flush stream);

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
  read_line stream |> Option.map (parse_header #> map (read_chunk stream));


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
      write stream
        ((if n > 100 orelse exists_string (fn s => s = "\n") msg
          then make_header [n + 1] else []) @ [msg, "\n"]);
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
