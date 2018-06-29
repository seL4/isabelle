(*  Title:      Pure/PIDE/session.ML
    Author:     Makarius

Prover session: persistent state of logic image.
*)

signature SESSION =
sig
  val init: string -> unit
  val get_name: unit -> string
  val welcome: unit -> string
  val shutdown: unit -> unit
  val finish: unit -> unit
  val print_context_tracing: (Context.generic -> bool) -> unit
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

fun description () = (case get_name () of "" => "Isabelle" | name => "Isabelle/" ^ name);

fun welcome () = "Welcome to " ^ description () ^ Isabelle_System.isabelle_heading ();


(* finish *)

val shutdown_hooks : (unit -> unit) list Synchronized.var =
    Synchronized.var "Session.shutdown_hooks" [];

fun register_raw_shutdown_hook h =
  (Synchronized.change shutdown_hooks (fn hs => hs @ [h]);
   ());

fun register_shutdown_hook h =
  register_raw_shutdown_hook (fn () => (Exn.capture_body h; ()))

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
  ignore (Context.finish_tracing ()));

fun print_context_tracing pred =
  List.app (writeln o Proof_Display.print_context_tracing)
    (filter (pred o #1) (#contexts (Context.finish_tracing ())));

end;
