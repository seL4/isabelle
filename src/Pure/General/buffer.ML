(*  Title:      Pure/General/buffer.ML
    ID:         $Id$
    Author:     Markus Wenzel, TU Muenchen

Simple string buffers.
*)

signature BUFFER =
sig
  type T
  val empty: T
  val add: string -> T -> T
  val content: T -> string
  val write: Path.T -> T -> unit
end;

structure Buffer: BUFFER =
struct

datatype T = Buffer of string list;

val empty = Buffer [];
fun add x (Buffer xs) = Buffer (x :: xs);
fun content (Buffer xs) = implode (rev xs);
fun write path buffer = File.write path (content buffer);

end;
