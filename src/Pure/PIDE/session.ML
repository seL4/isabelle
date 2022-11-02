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

fun shutdown () =
 (Execution.shutdown ();
  Event_Timer.shutdown ();
  Future.shutdown ());

fun finish () =
 (shutdown ();
  Par_List.map (Global_Theory.get_thm_names o Thy_Info.get_theory) (Thy_Info.get_names ());
  Thy_Info.finish ();
  shutdown ());

end;
