(*  Title:      Pure/PIDE/document.ML
    Author:     Makarius

Document as collection of named nodes, each consisting of an editable
list of commands.
*)

signature DOCUMENT =
sig
  type state_id = int
  type command_id = int
  type version_id = int
  val no_id: int
  val parse_id: string -> int
  val print_id: int -> string
  type edit = string * ((command_id * command_id option) list) option
end;

structure Document: DOCUMENT =
struct

(* unique identifiers *)

type state_id = int;
type command_id = int;
type version_id = int;

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

