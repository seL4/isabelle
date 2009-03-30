(*  Title:      HOL/Tools/atp_manager.ML
    Author:     Fabian Immler, TU Muenchen

ATP threads are registered here.
Threads with the same birth-time are seen as one group.
All threads of a group are killed when one thread of it has been successful,
or after a certain time,
or when the maximum number of threads exceeds; then the oldest thread is killed.
*)

signature ATP_MANAGER =
sig
  val get_atps: unit -> string
  val set_atps: string -> unit
  val get_max_atps: unit -> int
  val set_max_atps: int -> unit
  val get_timeout: unit -> int
  val set_timeout: int -> unit
  val kill: unit -> unit
  val info: unit -> unit
  val messages: int option -> unit
  type prover = int -> int -> Proof.context * (thm list * thm) -> bool * string
  val add_prover: string -> prover -> theory -> theory
  val print_provers: theory -> unit
  val sledgehammer: string list -> Proof.state -> unit
end;

structure AtpManager: ATP_MANAGER =
struct

(** preferences **)

val message_store_limit = 20;
val message_display_limit = 5;

local

val atps = ref "e remote_vampire";
val max_atps = ref 5;   (* ~1 means infinite number of atps *)
val timeout = ref 60;

in

fun get_atps () = CRITICAL (fn () => ! atps);
fun set_atps str = CRITICAL (fn () => atps := str);

fun get_max_atps () = CRITICAL (fn () => ! max_atps);
fun set_max_atps number = CRITICAL (fn () => max_atps := number);

fun get_timeout () = CRITICAL (fn () => ! timeout);
fun set_timeout time = CRITICAL (fn () => timeout := time);

val _ =
  ProofGeneralPgip.add_preference "Proof"
    (Preferences.string_pref atps
      "ATP: provers" "Default automatic provers (separated by whitespace)");

val _ = ProofGeneralPgip.add_preference "Proof"
    (Preferences.int_pref max_atps
      "ATP: maximum number" "How many provers may run in parallel");

val _ = ProofGeneralPgip.add_preference "Proof"
    (Preferences.int_pref timeout
      "ATP: timeout" "ATPs will be interrupted after this time (in seconds)");

end;



(** thread management **)

(* data structures over threads *)

structure ThreadHeap = HeapFun
(
  type elem = Time.time * Thread.thread;
  fun ord ((a, _), (b, _)) = Time.compare (a, b);
);

val lookup_thread = AList.lookup Thread.equal;
val delete_thread = AList.delete Thread.equal;
val update_thread = AList.update Thread.equal;


(* state of thread manager *)

datatype T = State of
 {timeout_heap: ThreadHeap.T,
  oldest_heap: ThreadHeap.T,
  active: (Thread.thread * (Time.time * Time.time * string)) list,
  cancelling: (Thread.thread * (Time.time * Time.time * string)) list,
  messages: string list,
  store: string list};

fun make_state timeout_heap oldest_heap active cancelling messages store =
  State {timeout_heap = timeout_heap, oldest_heap = oldest_heap,
    active = active, cancelling = cancelling, messages = messages, store = store};

fun empty_state state =
  let
    val State {active = active, cancelling = cancelling, messages = messages, ...} =
      Synchronized.value state
  in (null active) andalso (null cancelling) andalso (null messages) end;

val state = Synchronized.var "atp_manager" (make_state ThreadHeap.empty ThreadHeap.empty [] [] [] []);


(* the managing thread *)

(*watches over running threads and interrupts them if required*)
val managing_thread = ref (NONE: Thread.thread option);


(* unregister thread *)

fun unregister (success, message) thread = Synchronized.change state
  (fn state as State {timeout_heap, oldest_heap, active, cancelling, messages, store} =>
    (case lookup_thread active thread of
      SOME (birthtime, _, description) =>
        let
          val (group, active') =
            if success then List.partition (fn (_, (tb, _, _)) => tb = birthtime) active
            else List.partition (fn (th, _) => Thread.equal (th, thread)) active

          val now = Time.now ()
          val cancelling' =
            fold (fn (th, (tb, _, desc)) => update_thread (th, (tb, now, desc))) group cancelling

          val message' = description ^ "\n" ^ message ^
            (if length group <= 1 then ""
             else "\nInterrupted " ^ string_of_int (length group - 1) ^ " other group members")
          val store' = message' ::
            (if length store <= message_store_limit then store
             else #1 (chop message_store_limit store))
        in make_state timeout_heap oldest_heap active' cancelling' (message' :: messages) store' end
    | NONE => state));


(* kill excessive atp threads *)

fun excessive_atps active =
  let val max = get_max_atps ()
  in length active > max andalso max > ~1 end;

local

fun kill_oldest () =
  let exception Unchanged in
    Synchronized.change_result state
      (fn State {timeout_heap, oldest_heap, active, cancelling, messages, store} =>
        if ThreadHeap.is_empty oldest_heap orelse not (excessive_atps active)
        then raise Unchanged
        else
          let val ((_, oldest_thread), oldest_heap') = ThreadHeap.min_elem oldest_heap
          in (oldest_thread, make_state timeout_heap oldest_heap' active cancelling messages store) end)
      |> unregister (false, "Interrupted (maximum number of ATPs exceeded)")
    handle Unchanged => ()
  end;

in

fun kill_excessive () =
  let val State {active, ...} = Synchronized.value state
  in if excessive_atps active then (kill_oldest (); kill_excessive ()) else () end;

end;

fun print_new_messages () =
  let val to_print = Synchronized.change_result state
    (fn State {timeout_heap, oldest_heap, active, cancelling, messages, store} =>
      (messages, make_state timeout_heap oldest_heap active cancelling [] store))
  in
    if null to_print then ()
    else priority ("Sledgehammer: " ^ space_implode "\n\n" to_print)
  end;


(* start a watching thread -- only one may exist *)

fun check_thread_manager () = CRITICAL (fn () =>
  if (case ! managing_thread of SOME thread => Thread.isActive thread | NONE => false)
  then () else managing_thread := SOME (SimpleThread.fork false (fn () =>
    let
      val min_wait_time = Time.fromMilliseconds 300
      val max_wait_time = Time.fromSeconds 10

      (* wait for next thread to cancel, or maximum*)
      fun time_limit (State {timeout_heap, ...}) =
        (case try ThreadHeap.min timeout_heap of
          NONE => SOME (Time.+ (Time.now (), max_wait_time))
        | SOME (time, _) => SOME time)

      (* action: find threads whose timeout is reached, and interrupt cancelling threads *)
      fun action (State {timeout_heap, oldest_heap, active, cancelling, messages, store}) =
        let val (timeout_threads, timeout_heap') =
          ThreadHeap.upto (Time.now (), Thread.self ()) timeout_heap
        in
          if null timeout_threads andalso null cancelling andalso not (excessive_atps active)
          then NONE
          else
            let
              val _ = List.app (SimpleThread.interrupt o #1) cancelling
              val cancelling' = filter (Thread.isActive o #1) cancelling
              val state' = make_state timeout_heap' oldest_heap active cancelling' messages store
            in SOME (map #2 timeout_threads, state') end
        end
    in
      while not (empty_state state) do
       (Synchronized.timed_access state time_limit action
        |> these
        |> List.app (unregister (false, "Interrupted (reached timeout)"));
        kill_excessive ();
        print_new_messages ();
        (*give threads time to respond to interrupt*)
        OS.Process.sleep min_wait_time)
    end)));


(* thread is registered here by sledgehammer *)

fun register birthtime deadtime (thread, desc) =
 (Synchronized.change state
    (fn State {timeout_heap, oldest_heap, active, cancelling, messages, store} =>
      let
        val timeout_heap' = ThreadHeap.insert (deadtime, thread) timeout_heap
        val oldest_heap' = ThreadHeap.insert (birthtime, thread) oldest_heap
        val active' = update_thread (thread, (birthtime, deadtime, desc)) active
      in make_state timeout_heap' oldest_heap' active' cancelling messages store end);
  check_thread_manager ());



(** user commands **)

(* kill: move all threads to cancelling *)

fun kill () = Synchronized.change state
  (fn State {timeout_heap, oldest_heap, active, cancelling, messages, store} =>
    let val formerly_active = map (fn (th, (tb, _, desc)) => (th, (tb, Time.now (), desc))) active
    in make_state timeout_heap oldest_heap [] (formerly_active @ cancelling) messages store end);


(* ATP info *)

fun info () =
  let
    val State {active, cancelling, ...} = Synchronized.value state

    fun running_info (_, (birth_time, dead_time, desc)) = "Running: "
        ^ (string_of_int o Time.toSeconds) (Time.- (Time.now (), birth_time))
        ^ " s  --  "
        ^ (string_of_int o Time.toSeconds) (Time.- (dead_time, Time.now ()))
        ^ " s to live:\n" ^ desc
    fun cancelling_info (_, (_, dead_time, desc)) = "Trying to interrupt thread since "
        ^ (string_of_int o Time.toSeconds) (Time.- (Time.now (), dead_time))
        ^ " s:\n" ^ desc

    val running =
      if null active then "No ATPs running."
      else space_implode "\n\n" ("Running ATPs:" :: map running_info active)
    val interrupting =
      if null cancelling then ""
      else space_implode "\n\n"
        ("Trying to interrupt the following ATPs:" :: map cancelling_info cancelling)

  in writeln (running ^ "\n" ^ interrupting) end;

fun messages opt_limit =
  let
    val limit = the_default message_display_limit opt_limit;
    val State {store = msgs, ...} = Synchronized.value state
    val header = "Recent ATP messages" ^
      (if length msgs <= limit then ":" else " (" ^ string_of_int limit ^ " displayed):");
  in writeln (space_implode "\n\n" (header :: #1 (chop limit msgs))) end;



(** The Sledgehammer **)

(* named provers *)

type prover = int -> int -> Proof.context * (thm list * thm) -> bool * string;

fun err_dup_prover name = error ("Duplicate prover: " ^ quote name);

structure Provers = TheoryDataFun
(
  type T = (prover * stamp) Symtab.table
  val empty = Symtab.empty
  val copy = I
  val extend = I
  fun merge _ tabs : T = Symtab.merge (eq_snd op =) tabs
    handle Symtab.DUP dup => err_dup_prover dup
);

fun add_prover name prover thy =
  Provers.map (Symtab.update_new (name, (prover, stamp ()))) thy
    handle Symtab.DUP dup => err_dup_prover dup;

fun print_provers thy = Pretty.writeln
  (Pretty.strs ("external provers:" :: sort_strings (Symtab.keys (Provers.get thy))));


(* start prover thread *)

fun start_prover name birthtime deadtime i proof_state =
  (case Symtab.lookup (Provers.get (Proof.theory_of proof_state)) name of
    NONE => warning ("Unknown external prover: " ^ quote name)
  | SOME (prover, _) =>
      let
        val (ctxt, (_, goal)) = Proof.get_goal proof_state
        val desc =
          "external prover " ^ quote name ^ " for subgoal " ^ string_of_int i ^ ":\n" ^
            Syntax.string_of_term ctxt (Thm.term_of (Thm.cprem_of goal i))
        val _ = SimpleThread.fork true (fn () =>
          let
            val _ = register birthtime deadtime (Thread.self (), desc)
            val result = prover (get_timeout ()) i (Proof.get_goal proof_state)
              handle ResHolClause.TOO_TRIVIAL
                => (true, "Empty clause: Try this command: " ^ Markup.markup Markup.sendback "apply metis")
              | ERROR msg
                => (false, "Error: " ^ msg)
            val _ = unregister result (Thread.self ())
          in () end handle Interrupt => ())
      in () end);


(* sledghammer for first subgoal *)

fun sledgehammer names proof_state =
  let
    val provers =
      if null names then String.tokens (Symbol.is_ascii_blank o String.str) (get_atps ())
      else names
    val birthtime = Time.now ()
    val deadtime = Time.+ (birthtime, Time.fromSeconds (get_timeout ()))
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

