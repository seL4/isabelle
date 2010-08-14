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

fun parse_id s =
  (case Int.fromString s of
    SOME i => i
  | NONE => raise Fail ("Bad id: " ^ quote s));

val print_id = signed_string_of_int;


(* edits *)

type edit =
  string *  (*node name*)
  ((command_id * command_id option) list) option;  (*NONE: remove, SOME: insert/remove commands*)

end;

