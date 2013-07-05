(*  Title:      Pure/PIDE/document_id.ML
    Author:     Makarius

Unique identifiers for document structure.

NB: ML ticks forwards > 0, JVM ticks backwards < 0.
*)

signature DOCUMENT_ID =
sig
  type id = int
  type version = id
  type command = id
  type exec = id
  val none: id
  val make: unit -> id
  val parse: string -> id
  val print: id -> string
end;

structure Document_ID: DOCUMENT_ID =
struct

type id = int;
type version = id;
type command = id;
type exec = id;

val none = 0;
val make = Synchronized.counter ();

val parse = Markup.parse_int;
val print = Markup.print_int;

end;

