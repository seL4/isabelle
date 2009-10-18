(*  Title:      HOL/Tools/ATP_Manager/atp_manager.ML
    Author:     Fabian Immler, TU Muenchen

ATP threads are registered here.
Threads with the same birth-time are seen as one group.
All threads of a group are killed when one thread of it has been successful,
or after a certain time,
or when the maximum number of threads exceeds; then the oldest thread is killed.
*)

signature ATP_MANAGER =
sig
  val atps: string Unsynchronized.ref
  val get_atps: unit -> string list
  val max_atps: int Unsynchronized.ref
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

val max_atps = Unsynchronized.ref 5;
fun excessive_atps active =
  let val max = ! max_atps
  in max >= 0 andalso length active > max end;

val timeout = Unsynchronized.ref 60;
val full_types = Unsynchronized.ref false;

val _ =
  ProofGeneralPgip.add_preference Preferences.category_proof
    (Preferences.string_pref atps
      "ATP: provers" "Default automatic provers (separated by whitespace)");

val _ =
  ProofGeneralPgip.add_preference Preferences.category_proof
    (Preferences.int_pref max_atps
      "ATP: maximum number" "How many provers may run in parallel");

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
fun update_thread xs = AList.update Thread.equal xs;


(* state of thread manager *)

type state =
 {manager: Thread.thread option,
  timeout_heap: Thread_Heap.T,
  oldest_heap: Thread_Heap.T,
  active: (Thread.thread * (Time.time * Time.time * string)) list,
  cancelling: (Thread.thread * (Time.time * Time.time * string)) list,
  messages: string list,
  store: string list};

fun make_state manager timeout_heap oldest_heap active cancelling messages store : state =
  {manager = manager, timeout_heap = timeout_heap, oldest_heap = oldest_heap,
    active = active, cancelling = cancelling, messages = messages, store = store};

val global_state = Synchronized.var "atp_manager"
  (make_state NONE Thread_Heap.empty Thread_Heap.empty [] [] [] []);


(* unregister thread *)

fun unregister (success, message) thread = Synchronized.change global_state
  (fn state as {manager, timeout_heap, oldest_heap, active, cancelling, messages, store} =>
    (case lookup_thread active thread of
      SOME (birthtime, _, description) =>
        let
          val (group, active') =
            if success then List.partition (fn (_, (tb, _, _)) => tb = birthtime) active
            else List.partition (fn (th, _) => Thread.equal (th, thread)) active;

          val now = Time.now ();
          val cancelling' =
            fold (fn (th, (tb, _, desc)) => update_thread (th, (tb, now, desc))) group cancelling;

          val message' = description ^ "\n" ^ message ^
            (if length group <= 1 then ""
             else "\nInterrupted " ^ string_of_int (length group - 1) ^ " other group members");
          val store' = message' ::
            (if length store <= message_store_limit then store
             else #1 (chop message_store_limit store));
        in
          make_state manager timeout_heap oldest_heap
            active' cancelling' (message' :: messages) store'
        end
    | NONE => state));


(* kill excessive atp threads *)

local

exception UNCHANGED of unit;

fun kill_oldest () =
  Synchronized.change_result global_state
    (fn {manager, timeout_heap, oldest_heap, active, cancelling, messages, store} =>
      if Thread_Heap.is_empty oldest_heap orelse not (excessive_atps active)
      then raise UNCHANGED ()
      else
        let
          val ((_, oldest_thread), oldest_heap') = Thread_Heap.min_elem oldest_heap;
          val state' =
            make_state manager timeout_heap oldest_heap' active cancelling messages store;
        in (oldest_thread, state') end)
    |> unregister (false, "Interrupted (maximum number of ATPs exceeded)")
  handle UNCHANGED () => ();

in

fun kill_excessive () =
  let val {active, ...} = Synchronized.value global_state
  in if excessive_atps active then (kill_oldest (); kill_excessive ()) else () end;

end;

fun print_new_messages () =
  let val msgs = Synchronized.change_result global_state
    (fn {manager, timeout_heap, oldest_heap, active, cancelling, messages, store} =>
      (messages, make_state manager timeout_heap oldest_heap active cancelling [] store))
  in
    if null msgs then ()
    else priority ("Sledgehammer: " ^ space_implode "\n\n" msgs)
  end;


(* start manager thread -- only one may exist *)

val min_wait_time = Time.fromMilliseconds 300;
val max_wait_time = Time.fromSeconds 10;

fun check_thread_manager () = Synchronized.change global_state
  (fn {manager, timeout_heap, oldest_heap, active, cancelling, messages, store} =>
    if (case manager of SOME thread => Thread.isActive thread | NONE => false)
    then make_state manager timeout_heap oldest_heap active cancelling messages store
    else let val manager = SOME (SimpleThread.fork false (fn () =>
      let
        fun time_limit timeout_heap =
          (case try Thread_Heap.min timeout_heap of
            NONE => Time.+ (Time.now (), max_wait_time)
          | SOME (time, _) => time);

        (*action: find threads whose timeout is reached, and interrupt cancelling threads*)
        fun action {manager, timeout_heap, oldest_heap, active, cancelling, messages, store} =
          let val (timeout_threads, timeout_heap') =
            Thread_Heap.upto (Time.now (), Thread.self ()) timeout_heap;
          in
            if null timeout_threads andalso null cancelling andalso not (excessive_atps active)
            then NONE
            else
              let
                val _ = List.app (SimpleThread.interrupt o #1) cancelling;
                val cancelling' = filter (Thread.isActive o #1) cancelling;
                val state' =
                  make_state manager timeout_heap' oldest_heap active cancelling' messages store;
              in SOME (map #2 timeout_threads, state') end
          end;
      in
        while Synchronized.change_result global_state
          (fn state as {timeout_heap, oldest_heap, active, cancelling, messages, store, ...} =>
            if null active andalso null cancelling andalso null messages
            then (false, make_state NONE timeout_heap oldest_heap active cancelling messages store)
            else (true, state))
        do
          (Synchronized.timed_access global_state (SOME o time_limit o #timeout_heap) action
            |> these
            |> List.app (unregister (false, "Interrupted (reached timeout)"));
            kill_excessive ();
            print_new_messages ();
            (*give threads some time to respond to interrupt*)
            OS.Process.sleep min_wait_time)
      end))
    in make_state manager timeout_heap oldest_heap active cancelling messages store end);


(* thread is registered here by sledgehammer *)

fun register birthtime deadtime (thread, desc) =
 (Synchronized.change global_state
    (fn {manager, timeout_heap, oldest_heap, active, cancelling, messages, store} =>
      let
        val timeout_heap' = Thread_Heap.insert (deadtime, thread) timeout_heap;
        val oldest_heap' = Thread_Heap.insert (birthtime, thread) oldest_heap;
        val active' = update_thread (thread, (birthtime, deadtime, desc)) active;
        val state' =
          make_state manager timeout_heap' oldest_heap' active' cancelling messages store;
      in state' end);
  check_thread_manager ());



(** user commands **)

(* kill: move all threads to cancelling *)

fun kill () = Synchronized.change global_state
  (fn {manager, timeout_heap, oldest_heap, active, cancelling, messages, store} =>
    let
      val killing = map (fn (th, (tb, _, desc)) => (th, (tb, Time.now (), desc))) active;
      val state' =
        make_state manager timeout_heap oldest_heap [] (killing @ cancelling) messages store;
    in state' end);


(* ATP info *)

fun seconds time = string_of_int (Time.toSeconds time) ^ "s";

fun info () =
  let
    val {active, cancelling, ...} = Synchronized.value global_state;

    val now = Time.now ();
    fun running_info (_, (birth_time, dead_time, desc)) =
      "Running: " ^ seconds (Time.- (now, birth_time)) ^ " -- " ^
        seconds (Time.- (dead_time, now)) ^ " to live:\n" ^ desc;
    fun cancelling_info (_, (_, dead_time, desc)) =
      "Trying to interrupt thread since " ^ seconds (Time.- (now, dead_time)) ^ ":\n" ^ desc;

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

fun start_prover name birthtime deadtime i proof_state =
  (case get_prover (Proof.theory_of proof_state) name of
    NONE => warning ("Unknown external prover: " ^ quote name)
  | SOME prover =>
      let
        val full_goal as (ctxt, (_, goal)) = Proof.get_goal proof_state;
        val desc =
          "external prover " ^ quote name ^ " for subgoal " ^ string_of_int i ^ ":\n" ^
            Syntax.string_of_term ctxt (Thm.term_of (Thm.cprem_of goal i));
        val _ = SimpleThread.fork true (fn () =>
          let
            val _ = register birthtime deadtime (Thread.self (), desc);
            val problem = ATP_Wrapper.problem_of_goal (! full_types) i full_goal;
            val result =
              let val {success, message, ...} = prover (! timeout) problem;
              in (success, message) end
              handle ResHolClause.TOO_TRIVIAL =>   (* FIXME !? *)
                  (true, "Empty clause: Try this command: " ^
                    Markup.markup Markup.sendback "apply metis")
                | ERROR msg => (false, "Error: " ^ msg);
            val _ = unregister result (Thread.self ());
          in () end handle Exn.Interrupt => ())
      in () end);


(* sledghammer for first subgoal *)

fun sledgehammer names proof_state =
  let
    val provers = if null names then get_atps () else names;
    val birthtime = Time.now ();
    val deadtime = Time.+ (birthtime, Time.fromSeconds (! timeout));
  in List.app (fn name => start_prover name birthtime deadtime 1 proof_state) provers end;



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

