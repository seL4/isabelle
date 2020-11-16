(*  Title:      Pure/PIDE/session.ML
    Author:     Makarius

Prover session: persistent state of logic image.
*)

signature SESSION =
sig
  val get_name: unit -> string
  val welcome: unit -> string
  val get_keywords: unit -> Keyword.keywords
  val init: bool -> Path.T -> string list -> string -> string * string -> bool -> unit
  val shutdown: unit -> unit
  val finish: unit -> unit
end;

structure Session: SESSION =
struct

(** persistent session information **)

val session = Synchronized.var "Session.session" ({chapter = "", name = ""}, true);

fun get_name () = #name (#1 (Synchronized.value session));

fun description () = "Isabelle/" ^ get_name ();

fun welcome () =
  if Distribution.is_identified then
    "Welcome to " ^ description () ^ " (" ^ Distribution.version ^ ")"
  else "Unofficial version of " ^ description () ^ " (" ^ Distribution.version ^ ")";


(* base syntax *)

val keywords = Synchronized.var "Session.keywords" Keyword.empty_keywords;

fun get_keywords () = Synchronized.value keywords;

fun update_keywords () =
  Synchronized.change keywords
    (K (fold (curry Keyword.merge_keywords o Thy_Header.get_keywords o Thy_Info.get_theory)
      (Thy_Info.get_names ()) Keyword.empty_keywords));


(* init *)

fun init info info_path documents parent (chapter, name) verbose =
  (Synchronized.change session (fn ({name = parent_name, ...}, parent_finished) =>
    if parent_name <> parent orelse not parent_finished then
      error ("Unfinished parent session " ^ quote parent ^ " for " ^ quote name)
    else ({chapter = chapter, name = name}, false));
    Present.init info info_path documents (chapter, name) verbose);


(* finish *)

fun shutdown () =
 (Execution.shutdown ();
  Event_Timer.shutdown ();
  Future.shutdown ());

fun finish () =
 (shutdown ();
  Par_List.map (Global_Theory.get_thm_names o Thy_Info.get_theory) (Thy_Info.get_names ());
  Thy_Info.finish ();
  Present.finish ();
  shutdown ();
  update_keywords ();
  Synchronized.change session (apsnd (K true)));

end;
