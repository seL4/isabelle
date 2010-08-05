(*  Title:      Pure/PIDE/document.ML
    Author:     Makarius

Document as collection of named nodes, each consisting of an editable
list of commands.
*)

signature DOCUMENT =
sig
  type state_id = string
  type command_id = string
  type version_id = string
  val no_id: string
  type edit = string * ((command_id * command_id option) list) option
end;

structure Document: DOCUMENT =
struct

(* unique identifiers *)

type state_id = string;
type command_id = string;
type version_id = string;

val no_id = "";


(* edits *)

type edit =
  string *  (*node name*)
  ((command_id * command_id option) list) option;  (*NONE: remove, SOME: insert/remove commands*)

end;

