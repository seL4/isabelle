(*  Title:      Pure/General/buffer.ML
    ID:         $Id$
    Author:     Markus Wenzel, TU Muenchen

Efficient string buffers.
*)

signature BUFFER =
sig
  type T
  val empty: T
  val add: string -> T -> T
  val content: T -> string
  val write: Path.T -> T -> unit
  val output: (string -> unit) -> T -> unit
end;

structure Buffer: BUFFER =
struct

datatype T = Buffer of string list;

val empty = Buffer [];

fun add "" buf = buf
  | add x (Buffer xs) = Buffer (x :: xs);

fun content (Buffer xs) = implode (rev xs);

fun write path (Buffer xs) = File.write_list path (rev xs);

fun output f (Buffer xs) = List.app f (rev xs);

end;
