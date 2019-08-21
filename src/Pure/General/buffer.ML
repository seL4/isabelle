(*  Title:      Pure/General/buffer.ML
    Author:     Makarius

Scalable text buffers.
*)

signature BUFFER =
sig
  type T
  val empty: T
  val chunks: T -> string list
  val content: T -> string
  val add: string -> T -> T
  val markup: Markup.T -> (T -> T) -> T -> T
  val output: T -> BinIO.outstream -> unit
end;

structure Buffer: BUFFER =
struct

abstype T = Buffer of {chunk_size: int, chunk: string list, buffer: string list}
with

val empty = Buffer {chunk_size = 0, chunk = [], buffer = []};

local
  val chunk_limit = 4096;

  fun add_chunk [] buffer = buffer
    | add_chunk chunk buffer = implode (rev chunk) :: buffer;
in

fun chunks (Buffer {chunk, buffer, ...}) = rev (add_chunk chunk buffer);

val content = implode o chunks;

fun add x (buf as Buffer {chunk_size, chunk, buffer}) =
  let val n = size x in
    if n = 0 then buf
    else if n + chunk_size < chunk_limit then
      Buffer {chunk_size = n + chunk_size, chunk = x :: chunk, buffer = buffer}
    else
      Buffer {chunk_size = 0, chunk = [],
        buffer =
          if n < chunk_limit
          then add_chunk (x :: chunk) buffer
          else x :: add_chunk chunk buffer}
  end;

end;

end;

fun markup m body =
  let val (bg, en) = Markup.output m
  in add bg #> body #> add en end;

fun output buf stream =
  List.app (fn s => BinIO.output (stream, Byte.stringToBytes s)) (chunks buf);

end;
