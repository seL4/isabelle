(*  Title:      Pure/General/buffer.ML
    Author:     Markus Wenzel, TU Muenchen

Efficient text buffers.
*)

signature BUFFER =
sig
  type T
  val empty: T
  val add: string -> T -> T
  val markup: Markup.T -> (T -> T) -> T -> T
  val content: T -> string
  val chunks: T -> string list
  val output: T -> BinIO.outstream -> unit
end;

structure Buffer: BUFFER =
struct

datatype T = Buffer of string list;

val empty = Buffer [];

fun add "" buf = buf
  | add x (Buffer xs) = Buffer (x :: xs);

fun markup m body =
  let val (bg, en) = Markup.output m
  in add bg #> body #> add en end;

fun content (Buffer xs) = implode (rev xs);


(* chunks *)

local

val max_chunk = 4096;

fun add_chunk [] res = res
  | add_chunk chunk res = implode chunk :: res;

fun rev_chunks [] _ chunk res = add_chunk chunk res
  | rev_chunks (x :: xs) len chunk res =
      let
        val n = size x;
        val len' = len + n;
      in
        if len' < max_chunk then rev_chunks xs len' (x :: chunk) res
        else rev_chunks xs n [x] (add_chunk chunk res)
      end;

in

fun chunks (Buffer xs) = rev_chunks xs 0 [] [];

fun output buf stream =
  List.app (fn s => BinIO.output (stream, Byte.stringToBytes s)) (chunks buf);

end;

end;
