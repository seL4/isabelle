(*  Title:      Pure/PIDE/document.ML
    Author:     Makarius

Document as collection of named nodes, each consisting of an editable
list of commands.
*)

signature DOCUMENT =
sig
  type id = int
  type version_id = id
  type command_id = id
  type exec_id = id
  val no_id: id
  val parse_id: string -> id
  val print_id: id -> string
  type edit = string * ((command_id * command_id option) list) option
end;

structure Document: DOCUMENT =
struct

(* unique identifiers *)

type id = int;
type version_id = id;
type command_id = id;
type exec_id = id;

val no_id = 0;

val parse_id = Markup.parse_int;
val print_id = Markup.print_int;


(* edits *)

type edit =
  string *  (*node name*)
  ((command_id * command_id option) list) option;  (*NONE: remove, SOME: insert/remove commands*)

end;

