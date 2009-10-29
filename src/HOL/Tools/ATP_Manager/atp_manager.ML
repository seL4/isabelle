(*  Title:      HOL/Tools/ATP_Manager/atp_manager.ML
    Author:     Fabian Immler, TU Muenchen
    Author:     Makarius

Central manager component for ATP threads.
*)

signature ATP_MANAGER =
sig
  val atps: string Unsynchronized.ref
  val get_atps: unit -> string list
  val timeout: int Unsynchronized.ref
  val full_types: bool Unsynchronized.ref
  val kill: unit -> unit
  val info: unit -> unit
  val messages: int option -> unit
  val add_prover: string * ATP_Wrapper.prover -> theory -> theory
  val get_prover: theory -> string -> ATP_Wrapper.prover option
  val print_provers: theory -> unit
  val sledgehammer: string list -> Proof.state -> unit
end;

structure ATP_Manager: ATP_MANAGER =
struct

(** preferences **)

val message_store_limit = 20;
val message_display_limit = 5;

val atps = Unsynchronized.ref "e spass remote_vampire";
fun get_atps () = String.tokens (Symbol.is_ascii_blank o String.str) (! atps);

val timeout = Unsynchronized.ref 60;
val full_types = Unsynchronized.ref false;

val _ =
  ProofGeneralPgip.add_preference Preferences.category_proof
    (Preferences.string_pref atps
      "ATP: provers" "Default automatic provers (separated by whitespace)");

val _ =
  ProofGeneralPgip.add_preference Preferences.category_proof
    (Preferences.int_pref timeout
      "ATP: timeout" "ATPs will be interrupted after this time (in seconds)");

val _ =
  ProofGeneralPgip.add_preference Preferences.category_proof
    (Preferences.bool_pref full_types
      "ATP: full types" "ATPs will use full type information");



(** thread management **)

(* data structures over threads *)

structure Thread_Heap = Heap
(
  type elem = Time.time * Thread.thread;
  fun ord ((a, _), (b, _)) = Time.compare (a, b);
);

fun lookup_thread xs = AList.lookup Thread.equal xs;
fun delete_thread xs = AList.delete Thread.equal xs;
fun update_thread xs = AList.update Thread.equal xs;


(* state of thread manager *)

type state =
 {manager: Thread.thread option,
  timeout_heap: Thread_Heap.T,
  active: (Thread.thread * (Time.time * Time.time * string)) list,
  cancelling: (Thread.thread * (Time.time * string)) list,
  messages: string list,
  store: string list};

fun make_state manager timeout_heap active cancelling messages store : state =
  {manager = manager, timeout_heap = timeout_heap, active = active,
    cancelling = cancelling, messages = messages, store = store};

val global_state = Synchronized.var "atp_manager"
  (make_state NONE Thread_Heap.empty [] [] [] []);


(* unregister ATP thread *)

fun unregister message thread = Synchronized.change global_state
  (fn state as {manager, timeout_heap, active, cancelling, messages, store} =>
    (case lookup_thread active thread of
      SOME (birth_time, _, description) =>
        let
          val active' = delete_thread thread active;
          val cancelling' = (thread, (Time.now (), description)) :: cancelling;
          val message' = description ^ "\n" ^ message;
          val messages' = message' :: messages;
          val store' = message' ::
            (if length store <= message_store_limit then store
             else #1 (chop message_store_limit store));
        in make_state manager timeout_heap active' cancelling' messages' store' end
    | NONE => state));


(* main manager thread -- only one may exist *)

val min_wait_time = Time.fromMilliseconds 300;
val max_wait_time = Time.fromSeconds 10;

fun print_new_messages () =
  let val msgs = Synchronized.change_result global_state
    (fn {manager, timeout_heap, active, cancelling, messages, store} =>
      (messages, make_state manager timeout_heap active cancelling [] store))
  in
    if null msgs then ()
    else priority ("Sledgehammer: " ^ space_implode "\n\n" msgs)
  end;

fun check_thread_manager () = Synchronized.change global_state
  (fn state as {manager, timeout_heap, active, cancelling, messages, store} =>
    if (case manager of SOME thread => Thread.isActive thread | NONE => false) then state
    else let val manager = SOME (SimpleThread.fork false (fn () =>
      let
        fun time_limit timeout_heap =
          (case try Thread_Heap.min timeout_heap of
            NONE => Time.+ (Time.now (), max_wait_time)
          | SOME (time, _) => time);

        (*action: find threads whose timeout is reached, and interrupt cancelling threads*)
        fun action {manager, timeout_heap, active, cancelling, messages, store} =
          let val (timeout_threads, timeout_heap') =
            Thread_Heap.upto (Time.now (), Thread.self ()) timeout_heap;
          in
            if null timeout_threads andalso null cancelling
            then NONE
            else
              let
                val _ = List.app (SimpleThread.interrupt o #1) cancelling;
                val cancelling' = filter (Thread.isActive o #1) cancelling;
                val state' = make_state manager timeout_heap' active cancelling' messages store;
              in SOME (map #2 timeout_threads, state') end
          end;
      in
        while Synchronized.change_result global_state
          (fn state as {timeout_heap, active, cancelling, messages, store, ...} =>
            if null active andalso null cancelling andalso null messages
            then (false, make_state NONE timeout_heap active cancelling messages store)
            else (true, state))
        do
          (Synchronized.timed_access global_state (SOME o time_limit o #timeout_heap) action
            |> these
            |> List.app (unregister "Interrupted (reached timeout)");
            print_new_messages ();
            (*give threads some time to respond to interrupt*)
            OS.Process.sleep min_wait_time)
      end))
    in make_state manager timeout_heap active cancelling messages store end);


(* register ATP thread *)

fun register birth_time death_time (thread, desc) =
 (Synchronized.change global_state
    (fn {manager, timeout_heap, active, cancelling, messages, store} =>
      let
        val timeout_heap' = Thread_Heap.insert (death_time, thread) timeout_heap;
        val active' = update_thread (thread, (birth_time, death_time, desc)) active;
        val state' = make_state manager timeout_heap' active' cancelling messages store;
      in state' end);
  check_thread_manager ());



(** user commands **)

(* kill *)

fun kill () = Synchronized.change global_state
  (fn {manager, timeout_heap, active, cancelling, messages, store} =>
    let
      val killing = map (fn (th, (_, _, desc)) => (th, (Time.now (), desc))) active;
      val state' = make_state manager timeout_heap [] (killing @ cancelling) messages store;
    in state' end);


(* info *)

fun seconds time = string_of_int (Time.toSeconds time) ^ "s";

fun info () =
  let
    val {active, cancelling, ...} = Synchronized.value global_state;

    val now = Time.now ();
    fun running_info (_, (birth_time, death_time, desc)) =
      "Running: " ^ seconds (Time.- (now, birth_time)) ^ " -- " ^
        seconds (Time.- (death_time, now)) ^ " to live:\n" ^ desc;
    fun cancelling_info (_, (deadth_time, desc)) =
      "Trying to interrupt thread since " ^ seconds (Time.- (now, deadth_time)) ^ ":\n" ^ desc;

    val running =
      if null active then "No ATPs running."
      else space_implode "\n\n" ("Running ATPs:" :: map running_info active);
    val interrupting =
      if null cancelling then ""
      else
        space_implode "\n\n"
          ("Trying to interrupt the following ATPs:" :: map cancelling_info cancelling);

  in writeln (running ^ "\n" ^ interrupting) end;

fun messages opt_limit =
  let
    val limit = the_default message_display_limit opt_limit;
    val {store, ...} = Synchronized.value global_state;
    val header =
      "Recent ATP messages" ^
        (if length store <= limit then ":" else " (" ^ string_of_int limit ^ " displayed):");
  in writeln (space_implode "\n\n" (header :: #1 (chop limit store))) end;



(** The Sledgehammer **)

(* named provers *)

fun err_dup_prover name = error ("Duplicate prover: " ^ quote name);

structure Provers = TheoryDataFun
(
  type T = (ATP_Wrapper.prover * stamp) Symtab.table;
  val empty = Symtab.empty;
  val copy = I;
  val extend = I;
  fun merge _ tabs : T = Symtab.merge (eq_snd op =) tabs
    handle Symtab.DUP dup => err_dup_prover dup;
);

fun add_prover (name, prover) thy =
  Provers.map (Symtab.update_new (name, (prover, stamp ()))) thy
    handle Symtab.DUP dup => err_dup_prover dup;

fun get_prover thy name =
  Option.map #1 (Symtab.lookup (Provers.get thy) name);

fun print_provers thy = Pretty.writeln
  (Pretty.strs ("external provers:" :: sort_strings (Symtab.keys (Provers.get thy))));


(* start prover thread *)

fun start_prover name birth_time death_time i proof_state =
  (case get_prover (Proof.theory_of proof_state) name of
    NONE => warning ("Unknown external prover: " ^ quote name)
  | SOME prover =>
      let
        val {context = ctxt, facts, goal} = Proof.raw_goal proof_state; (* FIXME Proof.goal *)
        val desc =
          "external prover " ^ quote name ^ " for subgoal " ^ string_of_int i ^ ":\n" ^
            Syntax.string_of_term ctxt (Thm.term_of (Thm.cprem_of goal i));

        val _ = SimpleThread.fork true (fn () =>
          let
            val _ = register birth_time death_time (Thread.self (), desc);
            val problem = ATP_Wrapper.problem_of_goal (! full_types) i (ctxt, (facts, goal));
            val message = #message (prover (! timeout) problem)
              handle ResHolClause.TOO_TRIVIAL =>   (* FIXME !? *)
                  "Empty clause: Try this command: " ^ Markup.markup Markup.sendback "apply metis"
                | ERROR msg => ("Error: " ^ msg);
            val _ = unregister message (Thread.self ());
          in () end)
      in () end);


(* sledghammer for first subgoal *)

fun sledgehammer names proof_state =
  let
    val provers = if null names then get_atps () else names;
    val birth_time = Time.now ();
    val death_time = Time.+ (birth_time, Time.fromSeconds (! timeout));
    val _ = kill ();   (*RACE wrt. other invocations of sledgehammer*)
    val _ = List.app (fn name => start_prover name birth_time death_time 1 proof_state) provers;
  in () end;



(** Isar command syntax **)

local structure K = OuterKeyword and P = OuterParse in

val _ =
  OuterSyntax.improper_command "atp_kill" "kill all managed provers" K.diag
    (Scan.succeed (Toplevel.no_timing o Toplevel.imperative kill));

val _ =
  OuterSyntax.improper_command "atp_info" "print information about managed provers" K.diag
    (Scan.succeed (Toplevel.no_timing o Toplevel.imperative info));

val _ =
  OuterSyntax.improper_command "atp_messages" "print recent messages issued by managed provers" K.diag
    (Scan.option (P.$$$ "(" |-- P.nat --| P.$$$ ")") >>
      (fn limit => Toplevel.no_timing o Toplevel.imperative (fn () => messages limit)));

val _ =
  OuterSyntax.improper_command "print_atps" "print external provers" K.diag
    (Scan.succeed (Toplevel.no_timing o Toplevel.unknown_theory o
      Toplevel.keep (print_provers o Toplevel.theory_of)));

val _ =
  OuterSyntax.command "sledgehammer" "call all automatic theorem provers" K.diag
    (Scan.repeat P.xname >> (fn names => Toplevel.no_timing o Toplevel.unknown_proof o
      Toplevel.keep (sledgehammer names o Toplevel.proof_of)));

end;

end;

