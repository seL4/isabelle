(*  Title:      Pure/General/byte_message.ML
    Author:     Makarius

Byte-oriented messages.
*)

signature BYTE_MESSAGE =
sig
  val read_line: BinIO.instream -> string option
  val read_block: BinIO.instream -> int -> string
end;

structure Byte_Message: BYTE_MESSAGE =
struct

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

fun read_block stream n =
  Byte.bytesToString (BinIO.inputN (stream, n));

end;
