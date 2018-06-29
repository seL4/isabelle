(*  Title:      Pure/PIDE/session.ML
    Author:     Makarius

Prover session: persistent state of logic image.
*)

signature SESSION =
sig
  val init: string -> unit
  val get_name: unit -> string
  val welcome: unit -> string
  val get_keywords: unit -> Keyword.keywords
  val shutdown: unit -> unit
  val finish: unit -> unit
  (* Additional code to run before shutdown *)
  val register_shutdown_hook: (unit -> unit) -> unit
  (* Raw version, does not catch and ignore exceptions raised *)
  val register_raw_shutdown_hook: (unit -> unit) -> unit
end;

structure Session: SESSION =
struct

(* session name *)

val session = Synchronized.var "Session.session" "";

fun init name = Synchronized.change session (K name);

fun get_name () = Synchronized.value session;

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


(* finish *)

val shutdown_hooks : (unit -> unit) list Synchronized.var =
    Synchronized.var "Session.shutdown_hooks" [];

fun register_raw_shutdown_hook h =
  (Synchronized.change shutdown_hooks (fn hs => hs @ [h]);
   ());

fun register_shutdown_hook h =
  register_raw_shutdown_hook (fn () =>
    h () handle _ => ());

fun run_shutdown_hooks () =
  app (fn f => f ()) (Synchronized.value shutdown_hooks);

fun shutdown () =
 (Execution.shutdown ();
  Event_Timer.shutdown ();
  Future.shutdown ());

fun finish () =
 (shutdown ();
  Par_List.map (Global_Theory.get_thm_names o Thy_Info.get_theory) (Thy_Info.get_names ());
  Thy_Info.finish ();
  shutdown ();
  run_shutdown_hooks ();
  update_keywords ());

end;
