(*  Title:      Pure/System/session.ML
    Author:     Makarius

Session management -- internal state of logic images (not thread-safe).
*)

signature SESSION =
sig
  val name: unit -> string
  val welcome: unit -> string
  val init: bool -> bool -> Path.T -> string -> bool -> string -> (string * string) list ->
    string -> string * string -> bool * string -> bool -> unit
  val finish: unit -> unit
end;

structure Session: SESSION =
struct

(* session state *)

val session = Unsynchronized.ref {chapter = "Pure", name = "Pure"};
val session_finished = Unsynchronized.ref false;

fun name () = "Isabelle/" ^ #name (! session);

fun welcome () =
  if Distribution.is_official then
    "Welcome to " ^ name () ^ " (" ^ Distribution.version ^ ")"
  else "Unofficial version of " ^ name () ^ " (" ^ Distribution.version ^ ")";


(* init *)

fun init build info info_path doc doc_graph doc_output doc_variants
    parent (chapter, name) doc_dump verbose =
  if #name (! session) <> parent orelse not (! session_finished) then
    error ("Unfinished parent session " ^ quote parent ^ " for " ^ quote name)
  else
    let
      val _ = session := {chapter = chapter, name = name};
      val _ = session_finished := false;
    in
      Present.init build info info_path (if doc = "false" then "" else doc)
        doc_graph doc_output doc_variants (chapter, name)
        doc_dump verbose (map Thy_Info.get_theory (Thy_Info.get_names ()))
    end;


(* finish *)

fun finish () =
 (Goal.shutdown_futures ();
  Thy_Info.finish ();
  Present.finish ();
  Keyword.status ();
  Outer_Syntax.check_syntax ();
  Future.shutdown ();
  Event_Timer.shutdown ();
  session_finished := true);

end;
