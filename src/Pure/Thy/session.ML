(*  Title:      Pure/Thy/session.ML
    ID:         $Id$
    Author:     Markus Wenzel, TU Muenchen

Session management -- maintain state of logic images.
*)

signature SESSION =
sig
  val path: unit -> string list
  val welcome: unit -> string
  val use_dir: bool -> bool -> string -> unit
end;

structure Session: SESSION =
struct

(* session state *)

val session = ref ([]: string list);
val session_path = ref ([]: string list);
val session_finished = ref true;

fun path () = ! session_path;

fun add_path reset s =
  (session := ! session @ [s]; session_path := (if reset then [] else ! session));


(* diagnostics *)

fun str_of [] = "Pure"
  | str_of ids = space_implode "/" ids;

fun welcome () = "Welcome to Isabelle/" ^ str_of (! session) ^ " (" ^ version ^ ")";


(* init *)

fun init reset name =
  if not (! session_finished) then
    error ("Unfinished session " ^ quote (str_of (! session)) ^ " for logic " ^ quote name)
  else (add_path reset name; session_finished := false);


(* finish *)

fun finish () = (ThyInfo.finish_all (); session_finished := true);


(* use_dir *)	(* FIXME info *)

fun use_dir reset info name = (init reset name; Use.exit_use "ROOT.ML"; finish ());


end;
