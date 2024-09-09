(*  Title:      Pure/General/buffer.ML
    Author:     Makarius

Scalable text buffers.
*)

signature BUFFER =
sig
  type T
  val empty: T
  val is_empty: T -> bool
  val add: string -> T -> T
  val length: T -> int
  val contents: T -> string list
  val content: T -> string
  val build: (T -> T) -> T
  val build_content: (T -> T) -> string
end;

structure Buffer: BUFFER =
struct

abstype T = Buffer of string list
with

val empty = Buffer [];

fun is_empty (Buffer xs) = null xs;

fun add "" buf = buf
  | add x (Buffer xs) = Buffer (x :: xs);

fun length (Buffer xs) = fold (Integer.add o size) xs 0;

fun contents (Buffer xs) = rev xs;
val content = implode o contents;

fun build (f: T -> T) = f empty;
fun build_content f = build f |> content;

end;

end;
