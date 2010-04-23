(*  Title:      HOL/Tools/ATP_Manager/atp_manager.ML
    Author:     Fabian Immler, TU Muenchen
    Author:     Makarius
    Author:     Jasmin Blanchette, TU Muenchen

Central manager component for ATP threads.
*)

signature ATP_MANAGER =
sig
  type relevance_override = Sledgehammer_Fact_Filter.relevance_override
  type minimize_command = Sledgehammer_Proof_Reconstruct.minimize_command
  type params =
    {debug: bool,
     verbose: bool,
     overlord: bool,
     atps: string list,
     full_types: bool,
     explicit_apply: bool,
     respect_no_atp: bool,
     relevance_threshold: real,
     convergence: real,
     theory_relevant: bool option,
     higher_order: bool option,
     follow_defs: bool,
     isar_proof: bool,
     modulus: int,
     sorts: bool,
     timeout: Time.time,
     minimize_timeout: Time.time}
  type problem =
    {subgoal: int,
     goal: Proof.context * (thm list * thm),
     relevance_override: relevance_override,
     axiom_clauses: (thm * (string * int)) list option,
     filtered_clauses: (thm * (string * int)) list option}
  type prover_result =
    {success: bool,
     message: string,
     relevant_thm_names: string list,
     atp_run_time_in_msecs: int,
     proof: string,
     internal_thm_names: string Vector.vector,
     filtered_clauses: (thm * (string * int)) list}
  type prover =
    params -> minimize_command -> Time.time -> problem -> prover_result

  val atps: string Unsynchronized.ref
  val timeout: int Unsynchronized.ref
  val full_types: bool Unsynchronized.ref
  val kill_atps: unit -> unit
  val running_atps: unit -> unit
  val messages: int option -> unit
  val add_prover: string * prover -> theory -> theory
  val get_prover: theory -> string -> prover option
  val available_atps: theory -> unit
  val sledgehammer:
    params -> int -> relevance_override -> (string -> minimize_command)
    -> Proof.state -> unit
end;

structure ATP_Manager : ATP_MANAGER =
struct

open Sledgehammer_Util
open Sledgehammer_Fact_Filter
open Sledgehammer_Proof_Reconstruct

(** problems, results, provers, etc. **)

type params =
  {debug: bool,
   verbose: bool,
   overlord: bool,
   atps: string list,
   full_types: bool,
   explicit_apply: bool,
   respect_no_atp: bool,
   relevance_threshold: real,
   convergence: real,
   theory_relevant: bool option,
   higher_order: bool option,
   follow_defs: bool,
   isar_proof: bool,
   modulus: int,
   sorts: bool,
   timeout: Time.time,
   minimize_timeout: Time.time}

type problem =
  {subgoal: int,
   goal: Proof.context * (thm list * thm),
   relevance_override: relevance_override,
   axiom_clauses: (thm * (string * int)) list option,
   filtered_clauses: (thm * (string * int)) list option};

type prover_result =
  {success: bool,
   message: string,
   relevant_thm_names: string list,
   atp_run_time_in_msecs: int,
   proof: string,
   internal_thm_names: string Vector.vector,
   filtered_clauses: (thm * (string * int)) list};

type prover =
  params -> minimize_command -> Time.time -> problem -> prover_result


(** preferences **)

val message_store_limit = 20;
val message_display_limit = 5;

val atps = Unsynchronized.ref "e spass remote_vampire"; (* set in "ATP_Wrapper" *)
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

fun unregister ({verbose, ...} : params) message thread =
  Synchronized.change global_state
  (fn state as {manager, timeout_heap, active, cancelling, messages, store} =>
    (case lookup_thread active thread of
      SOME (birth_time, _, description) =>
        let
          val active' = delete_thread thread active;
          val now = Time.now ()
          val cancelling' = (thread, (now, description)) :: cancelling;
          val message' =
            description ^ "\n" ^ message ^
            (if verbose then
               "Total time: " ^ Int.toString (Time.toMilliseconds
                                          (Time.- (now, birth_time))) ^ " ms.\n"
             else
               "")
          val messages' = message' :: messages;
          val store' = message' ::
            (if length store <= message_store_limit then store
             else #1 (chop message_store_limit store));
        in make_state manager timeout_heap active' cancelling' messages' store' end
    | NONE => state));


(* main manager thread -- only one may exist *)

val min_wait_time = Time.fromMilliseconds 300;
val max_wait_time = Time.fromSeconds 10;

(* This is a workaround for Proof General's off-by-a-few sendback display bug,
   whereby "pr" in "proof" is not highlighted. *)
val break_into_chunks =
  map (replace_all "\n\n" "\000") #> maps (space_explode "\000")

fun print_new_messages () =
  case Synchronized.change_result global_state
         (fn {manager, timeout_heap, active, cancelling, messages, store} =>
             (messages, make_state manager timeout_heap active cancelling []
                                   store)) of
    [] => ()
  | msgs =>
    msgs |> break_into_chunks
         |> (fn msg :: msgs => "Sledgehammer: " ^ msg :: msgs)
         |> List.app priority

fun check_thread_manager params = Synchronized.change global_state
  (fn state as {manager, timeout_heap, active, cancelling, messages, store} =>
    if (case manager of SOME thread => Thread.isActive thread | NONE => false) then state
    else let val manager = SOME (Toplevel.thread false (fn () =>
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
            |> List.app (unregister params "Timed out.");
            print_new_messages ();
            (*give threads some time to respond to interrupt*)
            OS.Process.sleep min_wait_time)
      end))
    in make_state manager timeout_heap active cancelling messages store end);


(* register ATP thread *)

fun register params birth_time death_time (thread, desc) =
 (Synchronized.change global_state
    (fn {manager, timeout_heap, active, cancelling, messages, store} =>
      let
        val timeout_heap' = Thread_Heap.insert (death_time, thread) timeout_heap;
        val active' = update_thread (thread, (birth_time, death_time, desc)) active;
        val state' = make_state manager timeout_heap' active' cancelling messages store;
      in state' end);
  check_thread_manager params);



(** user commands **)

(* kill ATPs *)

fun kill_atps () = Synchronized.change global_state
  (fn {manager, timeout_heap, active, cancelling, messages, store} =>
    let
      val killing = map (fn (th, (_, _, desc)) => (th, (Time.now (), desc))) active;
      val state' = make_state manager timeout_heap [] (killing @ cancelling) messages store;
    in state' end);


(* running_atps *)

fun seconds time = string_of_int (Time.toSeconds time) ^ "s";

fun running_atps () =
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

  in priority (running ^ "\n" ^ interrupting) end;

fun messages opt_limit =
  let
    val limit = the_default message_display_limit opt_limit;
    val {store, ...} = Synchronized.value global_state;
    val header =
      "Recent ATP messages" ^
        (if length store <= limit then ":" else " (" ^ string_of_int limit ^ " displayed):");
  in List.app priority (header :: break_into_chunks (#1 (chop limit store))) end


(** The Sledgehammer **)

(* named provers *)

fun err_dup_prover name = error ("Duplicate prover: " ^ quote name ^ ".");

structure Provers = Theory_Data
(
  type T = (prover * stamp) Symtab.table;
  val empty = Symtab.empty;
  val extend = I;
  fun merge data : T = Symtab.merge (eq_snd op =) data
    handle Symtab.DUP name => err_dup_prover name;
);

fun add_prover (name, prover) thy =
  Provers.map (Symtab.update_new (name, (prover, stamp ()))) thy
    handle Symtab.DUP name => err_dup_prover name;

fun get_prover thy name =
  Option.map #1 (Symtab.lookup (Provers.get thy) name);

fun available_atps thy =
  priority ("Available ATPs: " ^
            commas (sort_strings (Symtab.keys (Provers.get thy))) ^ ".")


(* start prover thread *)

fun start_prover (params as {timeout, ...}) birth_time death_time i
                 relevance_override minimize_command proof_state name =
  (case get_prover (Proof.theory_of proof_state) name of
    NONE => warning ("Unknown ATP: " ^ quote name ^ ".")
  | SOME prover =>
      let
        val {context = ctxt, facts, goal} = Proof.goal proof_state;
        val n = Logic.count_prems (prop_of goal)
        val desc =
          "ATP " ^ quote name ^ " for subgoal " ^ string_of_int i ^ ":\n" ^
            Syntax.string_of_term ctxt (Thm.term_of (Thm.cprem_of goal i));

        val _ = Toplevel.thread true (fn () =>
          let
            val _ = register params birth_time death_time (Thread.self (), desc)
            val problem =
              {subgoal = i, goal = (ctxt, (facts, goal)),
               relevance_override = relevance_override, axiom_clauses = NONE,
               filtered_clauses = NONE}
            val message =
              #message (prover params (minimize_command name) timeout problem)
              handle Sledgehammer_HOL_Clause.TRIVIAL =>
                  metis_line i n []
                | ERROR msg => "Error: " ^ msg ^ ".\n";
            val _ = unregister params message (Thread.self ());
          in () end);
      in () end);


(* Sledgehammer the given subgoal *)

fun sledgehammer (params as {atps, timeout, ...}) i relevance_override
                 minimize_command proof_state =
  let
    val birth_time = Time.now ()
    val death_time = Time.+ (birth_time, timeout)
    val _ = kill_atps () (* RACE w.r.t. other invocations of Sledgehammer *)
    val _ = priority "Sledgehammering..."
    val _ = List.app (start_prover params birth_time death_time i
                                   relevance_override minimize_command
                                   proof_state) atps
  in () end

end;
