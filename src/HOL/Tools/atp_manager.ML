(*  Title:      HOL/Tools/atp_manager.ML
    ID:         $Id$
    Author:     Fabian Immler, TU Muenchen

ATP threads are registered here.
Threads with the same birth-time are seen as one group.
All threads of a group are killed when one thread of it has been successful,
or after a certain time,
or when the maximum number of threads exceeds; then the oldest thread is killed.
*)

signature ATP_MANAGER =
sig
  val kill_all: unit -> unit
  val info: unit -> unit
  val set_atps: string -> unit
  val set_max_atp: int -> unit
  val set_timeout: int -> unit
  val atp_thread: (unit -> 'a option) -> ('a -> string) -> Thread.thread
  val add_prover: string -> (int -> Proof.state -> Thread.thread) -> theory -> theory
  val print_provers: theory -> unit
  val sledgehammer: string list -> Proof.state -> unit
end;

structure AtpManager : ATP_MANAGER =
struct

(* data structures over threads *)

structure ThreadHeap = HeapFun
(
  type elem = Time.time * Thread.thread;
  fun ord ((a, _), (b, _)) = Time.compare (a, b);
)

val lookup_thread = AList.lookup Thread.equal;
val delete_thread = AList.delete Thread.equal;
val update_thread = AList.update Thread.equal;


(* state of thread manager *)

datatype T = State of
 {timeout_heap: ThreadHeap.T,
  oldest_heap: ThreadHeap.T,
  active: (Thread.thread * (Time.time * Time.time * string)) list,
  cancelling: (Thread.thread * (Time.time * Time.time * string)) list};

fun make_state timeout_heap oldest_heap active cancelling =
  State {timeout_heap = timeout_heap, oldest_heap = oldest_heap,
    active = active, cancelling = cancelling};

val state = Synchronized.var "atp_manager" (make_state ThreadHeap.empty ThreadHeap.empty [] []);


(* the thread manager thread *)

(*watches over running threads and interrupts them if required*)
val managing_thread = ref (NONE: Thread.thread option);


(* unregister thread from thread manager -- move to cancelling *)

fun unregister success message thread = Synchronized.change_result state
  (fn State {timeout_heap, oldest_heap, active, cancelling} =>
    let
      val info = lookup_thread active thread

      (* get birthtime of unregistering thread if successful - for group-killing*)
      val birthtime = case info of NONE => Time.zeroTime
        | SOME (tb, _, _) => if success then tb else Time.zeroTime

      (* move unregistering thread to cancelling *)
      val active' = delete_thread thread active
      val cancelling' = case info of NONE => cancelling
        | SOME (tb, _, desc) => update_thread (thread, (tb, Time.now (), desc)) cancelling

      (* move all threads of the same group to cancelling *)
      val group_threads = active |> map_filter (fn (th, (tb, _, desc)) =>
          if tb = birthtime then SOME (th, (tb, Time.now (), desc)) else NONE)
      val active'' = filter_out (fn (_, (tb, _, _)) => tb = birthtime) active'
      val cancelling'' = append group_threads cancelling'

      (* message for user *)
      val message' = case info of NONE => ""
        | SOME (_, _, desc) => "Sledgehammer: " ^ desc ^ "\n  " ^ message ^
          (if null group_threads then ""
           else "\nInterrupted " ^ Int.toString (length group_threads - 1) ^ " other group members")
    in (message', make_state timeout_heap oldest_heap active'' cancelling'') end);


(* start a watching thread which runs forever -- only one may exist *)

fun check_thread_manager () =
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

      (* action: cancel find threads whose timeout is reached, and interrupt cancelling threads *)
      fun action (State {timeout_heap, oldest_heap, active, cancelling}) =
        let val (timeout_threads, timeout_heap') =
          ThreadHeap.upto (Time.now (), Thread.self ()) timeout_heap
        in
          if null timeout_threads andalso null cancelling then NONE
          else
            let
              val _ = List.app (SimpleThread.interrupt o #1) cancelling
              val cancelling' = filter (Thread.isActive o #1) cancelling
              val state' = make_state timeout_heap' oldest_heap active cancelling'
            in SOME (map #2 timeout_threads, state') end
        end
    in
      while true do
       ((* cancel threads found by action *)
        Synchronized.timed_access state time_limit action
        |> these
        |> List.app (priority o unregister false "Interrupted (reached timeout)");
        (* give threads time to respond to interrupt *)
        OS.Process.sleep min_wait_time)
    end));


(* thread is registered here by sledgehammer *)

fun register birthtime deadtime (thread, desc) =
 (check_thread_manager ();
  Synchronized.change state (fn State {timeout_heap, oldest_heap, active, cancelling} =>
    let
      val timeout_heap' = ThreadHeap.insert (deadtime, thread) timeout_heap
      val oldest_heap' = ThreadHeap.insert (birthtime, thread) oldest_heap
      val active' = update_thread (thread, (birthtime, deadtime, desc)) active
    in make_state timeout_heap' oldest_heap' active' cancelling end));


(* move all threads to cancelling *)

fun kill_all () = Synchronized.change state
  (fn State {timeout_heap, oldest_heap, active, cancelling} =>
    let val formerly_active = map (fn (th, (tb, _, desc)) => (th, (tb, Time.now (), desc))) active
    in make_state timeout_heap oldest_heap [] (formerly_active @ cancelling) end);


(* information on running threads *)

fun info () =
  let
    val State {timeout_heap, oldest_heap, active, cancelling} = Synchronized.value state
    fun running_info (_, (birth_time, dead_time, desc)) = "Running: "
        ^ ((Int.toString o Time.toSeconds) (Time.- (Time.now (), birth_time)))
        ^ " s  --  "
        ^ ((Int.toString o Time.toSeconds) (Time.- (dead_time, Time.now ())))
        ^ " s to live:\n" ^ desc
    fun cancelling_info (_, (_, dead_time, desc)) = "Trying to interrupt thread since "
        ^ (Int.toString o Time.toSeconds) (Time.- (Time.now (), dead_time))
        ^ " s:\n" ^ desc
    val running = if null active then "No ATPs running."
      else String.concatWith "\n\n" ("--- RUNNING ATPs ---" ::
      (map (fn entry => running_info entry) active))
    val interrupting = if null cancelling then ""
      else String.concatWith "\n\n" ("--- TRYING TO INTERRUPT FOLLOWING ATPs ---" ::
      (map (fn entry => cancelling_info entry) cancelling))
  in writeln (running ^ "\n" ^ interrupting) end;


(* thread wrapping an atp-call *)

fun atp_thread call_prover produce_answer =
  SimpleThread.fork true (fn () =>
    let
      val result = call_prover ()
      val message = case result of NONE => "Failed."
          | SOME result => "Try this command: " ^ produce_answer result
    in priority (unregister (is_some result) message (Thread.self ()))
    end handle Interrupt => ());


(* preferences *)

val atps = ref "e spass";
val maximum_atps = ref 5;   (* ~1 means infinite number of atps*)
val timeout = ref 60;

fun set_atps str = CRITICAL (fn () => atps := str);
fun set_max_atp number = CRITICAL (fn () => maximum_atps := number);
fun set_timeout time = CRITICAL (fn () => timeout := time);

val _ = ProofGeneralPgip.add_preference "Proof"
    {name = "ATP - Provers (see print_atps)",
     descr = "Default automatic provers (seperated by whitespace)",
     default = !atps,
     pgiptype = PgipTypes.Pgipstring,
     get = fn () => !atps,
     set = set_atps}
    handle ERROR _ => warning "Preference already exists";

val _ = ProofGeneralPgip.add_preference "Proof"
    {name = "ATP - Maximum number",
     descr = "How many provers may run in parallel",
     default = Int.toString (! maximum_atps),
     pgiptype = PgipTypes.Pgipstring,
     get = fn () => Int.toString (! maximum_atps),
     set = fn str => set_max_atp (the_default 1 (Int.fromString str))}
    handle ERROR _ => warning "Preference already exists";

val _ = ProofGeneralPgip.add_preference "Proof"
    {name = "ATP - Timeout",
     descr = "ATPs will be interrupted after this time (in seconds)",
     default = Int.toString (! timeout),
     pgiptype = PgipTypes.Pgipstring,
     get = fn () => Int.toString (! timeout),
     set = fn str => set_timeout (the_default 60 (Int.fromString str))}
    handle ERROR _ => warning "Preference already exists";


(* named provers *)

fun err_dup_prover name = error ("Duplicate prover: " ^ quote name);

structure Provers = TheoryDataFun
(
  type T = ((int -> Proof.state -> Thread.thread) * stamp) Symtab.table
  val empty = Symtab.empty
  val copy = I
  val extend = I
  fun merge _ tabs : T = Symtab.merge (eq_snd op =) tabs
    handle Symtab.DUP dup => err_dup_prover dup;
);

fun add_prover name prover_fn =
  Provers.map (Symtab.update_new (name, (prover_fn, stamp ())))
    handle Symtab.DUP dup => err_dup_prover dup;

fun print_provers thy = Pretty.writeln
  (Pretty.strs ("external provers:" :: sort_strings (Symtab.keys (Provers.get thy))));

fun prover_desc state subgoal name =
   let val (ctxt, (chain_ths, goal)) = Proof.get_goal state
   in "External prover " ^ quote name ^ " for Subgoal " ^ Int.toString subgoal^ ":\n" ^ Syntax.string_of_term ctxt (List.nth(prems_of goal, subgoal-1)) end

fun run_prover state subgoal name =
  (case Symtab.lookup (Provers.get (Proof.theory_of state)) name of
    NONE => (warning ("Unknown external prover: " ^ quote name); NONE)
  | SOME (prover_fn, _) => SOME (prover_fn subgoal state, prover_desc state subgoal name));


(* kill excessive atp threads *)

local

fun excessive_atps active =
  let val max = ! maximum_atps
  in length active > max andalso max > ~1 end;

fun kill_oldest () =
  let exception Unchanged in
    Synchronized.change_result state (fn State {timeout_heap, oldest_heap, active, cancelling} =>
        if ThreadHeap.is_empty oldest_heap orelse not (excessive_atps active)
        then raise Unchanged
        else
          let val ((_, oldest_thread), oldest_heap') = ThreadHeap.min_elem oldest_heap
          in (oldest_thread, make_state timeout_heap oldest_heap' active cancelling) end)
      |> (priority o unregister false "Interrupted (Maximum number of ATPs exceeded).")
    handle Unchanged => ()
  end;

in

fun kill_excessive () =
  let val State {active, ...} = Synchronized.value state
  in if excessive_atps active then (kill_oldest (); kill_excessive ()) else () end;

end;


(* sledghammer for first subgoal *)

fun sledgehammer names proof_state =
  let
    val proverids =
      if null names then String.tokens (Symbol.is_ascii_blank o String.str) (! atps)
      else names
    val threads_names = map_filter (run_prover proof_state 1) proverids
    val birthtime = Time.now ()
    val deadtime = Time.+ (Time.now (), Time.fromSeconds (! timeout))
    val _ = List.app (register birthtime deadtime) threads_names
    val _ = kill_excessive ()
  in () end


(* concrete syntax *)

local structure K = OuterKeyword and P = OuterParse in

val _ =
  OuterSyntax.improper_command "atp_kill" "kill all managed provers" K.diag
    (Scan.succeed (Toplevel.no_timing o Toplevel.imperative kill_all));

val _ =
  OuterSyntax.improper_command "atp_info" "print information about managed provers" K.diag
    (Scan.succeed (Toplevel.no_timing o Toplevel.imperative info));

val _ =
  OuterSyntax.improper_command "print_atps" "print external provers" K.diag
    (Scan.succeed (Toplevel.no_timing o Toplevel.unknown_theory o
      Toplevel.keep (print_provers o Toplevel.theory_of)));

val _ =
  OuterSyntax.command "sledgehammer" "call all automatic theorem provers" K.diag
    (Scan.repeat P.xname >> (fn names => Toplevel.no_timing o Toplevel.unknown_proof o
    Toplevel.keep ((sledgehammer names) o Toplevel.proof_of)));

end;

end;
