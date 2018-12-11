(*  Title:      Pure/General/byte_message.ML
    Author:     Makarius

Byte-oriented messages.
*)

signature BYTE_MESSAGE =
sig
  val read_line: BinIO.instream -> string option
  val read: BinIO.instream -> int -> string
  val read_block: BinIO.instream -> int -> string option
  val read_message: BinIO.instream -> string list option
end;

structure Byte_Message: BYTE_MESSAGE =
struct

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


(* messages with multiple chunks (arbitrary content) *)

fun read_chunk stream n =
  let val (len, chunk) = `size (read stream n) in
    if len = n then chunk
    else
      error ("Malformed message chunk: unexpected EOF after " ^
        string_of_int len ^ " of " ^ string_of_int n ^ " bytes")
  end;

fun read_message stream =
  read_line stream |> Option.map (fn line =>
    let
      val ns = map Value.parse_nat (space_explode "," line)
        handle Fail _ => error ("Malformed message header: " ^ quote line);
    in map (read_chunk stream) ns end);

end;
