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
  val info: unit -> string
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

  structure ThreadHeap = HeapFun
  (
    type elem = Time.time * Thread.thread;
    fun ord ((a, _), (b, _)) = Time.compare (a, b);
  )

  (* state of threadmanager *)
  datatype T = State of {
      timeout_heap: ThreadHeap.T,
      oldest_heap: ThreadHeap.T,
      (* managed threads *)
      active: (Thread.thread * (Time.time * Time.time * string)) list,
      cancelling: (Thread.thread * (Time.time * Time.time * string)) list
  }
  val state = ref (State {
        timeout_heap = ThreadHeap.empty,
        oldest_heap = ThreadHeap.empty,
        active = [],
        cancelling = []})
      
  (* synchronizing *)
  val lock = Mutex.mutex ()
  val state_change = ConditionVar.conditionVar ()
  (* watches over running threads and interrupts them if required *)
  val managing_thread = ref (NONE: Thread.thread option);

  (* active and cancelling are association lists *)
  val lookup_th = AList.lookup Thread.equal;
  val delete_th = AList.delete Thread.equal;
  val update_th = AList.update Thread.equal;
    
    
  (* waiting for a condition, checking it after time or when signalled
     then changing state with returning a result *)
  fun protected_wait_change_result P time f = uninterruptible (fn restore => fn () =>
      let
      val _ = Mutex.lock lock;
      val _ = while not (P (! state)) do ConditionVar.waitUntil (state_change, lock, time (! state));
      val res = Exn.Result (restore (fn () => change_result state f) ()) handle exn => Exn.Exn exn
      val _ = ConditionVar.broadcast state_change;
      val _ = Mutex.unlock lock;
  in Exn.release res end) ()
  
  fun protected_change f = protected_wait_change_result (fn _ => true) (fn _ => Time.zeroTime) f;
  
  fun protected f = protected_change (`f);

  (* unregister Thread from Threadmanager = move to cancelling *)
  fun unregister success message thread = protected_change (fn State {timeout_heap, oldest_heap, active, cancelling} => 
    let
    val info = lookup_th active thread
    (* get birthtime of unregistering thread if successful - for group-killing*)
    val birthtime = case info of NONE => Time.zeroTime
      | SOME (tb, _, _) => if success then tb else Time.zeroTime
    (* move unregistering thread to cancelling *)
    val active' = delete_th thread active
    val cancelling' = case info of NONE => cancelling
      | SOME (tb, _, desc) => update_th (thread, (tb, Time.now(), desc)) cancelling
    (* move all threads of the same group to cancelling *)
    val group_threads = map_filter (fn (th, (tb, _, desc)) =>
        if tb = birthtime then SOME (th, (tb, Time.now(), desc)) else NONE)
      active 
    val active'' = filter_out (fn (_, (tb, _, _)) => tb = birthtime) active'
    val cancelling'' = append group_threads cancelling'
    (* message for user *)
    val message = case info of NONE => ""
      | SOME (_, _, desc) => "Sledgehammer: " ^ desc ^ "\n    " ^ message ^
        (if length group_threads > 1
        then "\n\nInterrupted " ^ Int.toString (length group_threads - 1) ^ " others of group."
        else "")
    in (message, State {timeout_heap = timeout_heap,
                  oldest_heap = oldest_heap,
                  active = active'',
                  cancelling = cancelling''})
    end)
    
  (* start a watching thread which runs forever - only one may exist => checked by register *)
  fun start () = managing_thread := SOME (SimpleThread.fork false (fn () =>
    let
    val min_wait_time = Time.fromMilliseconds 300
    val max_wait_time = Time.fromSeconds 10
    (* action is required when there are cancelling threads, or a thread is to be cancelled *)
    fun P (State {timeout_heap, oldest_heap, active, cancelling}) =
      length cancelling > 0  orelse
        (not (ThreadHeap.is_empty timeout_heap) andalso
        Time.< (#1 (ThreadHeap.min timeout_heap), Time.now ()))
    (* wait for next thread to cancel, or a maximum of 10 Seconds*)
    fun time (State {timeout_heap, oldest_heap, active, cancelling}) =
      if ThreadHeap.is_empty timeout_heap then Time.+ (Time.now(), max_wait_time)
      else #1 (ThreadHeap.min timeout_heap)
    (* action: cancel find threads whose timeout is reached, and interrupt cancelling threads *)
    fun action (State {timeout_heap, oldest_heap, active, cancelling}) =
      let
      (* find out threads wich reached their timeout *)
      fun find_threads (heap, threads) =
        if ThreadHeap.is_empty heap then (heap, threads) else
          let val (mintime, minthread) = ThreadHeap.min heap
          in if Time.> (mintime, Time.now())
            then (heap, threads)
            else find_threads (ThreadHeap.delete_min heap, minthread :: threads)
          end
      val (timeout_heap', timeout_threads) = find_threads (timeout_heap, [])
      val _ = List.app (SimpleThread.interrupt o fst) cancelling
      val cancelling' = filter (fn (t, _) => Thread.isActive t) cancelling
      (* return threads with timeout and changed state *)
      in (timeout_threads, State {timeout_heap = timeout_heap',
                    oldest_heap = oldest_heap,
                    active = active,
                    cancelling = cancelling'})
      end
    in while true do 
        (* cancel threads found by 'action' *)
        (map (priority o (unregister false "Interrupted (reached timeout)")) (protected_wait_change_result P time action);
        (* give threads time to respond to interrupt *)
        OS.Process.sleep min_wait_time)
    end))

  (* calling thread is registered here by sledgehammer *)
  fun register birthtime deadtime (thread, desc) = protected_change (
    fn State {timeout_heap, oldest_heap, active, cancelling} => 
    let val _ = (* create the atp-managing-thread if this is the first call to register *)
      if (case ! managing_thread of SOME thread => Thread.isActive thread | NONE => false)
      then () else start ()
    (* insertion *)
    in ((),State {timeout_heap = ThreadHeap.insert (deadtime, thread) timeout_heap,
                  oldest_heap = ThreadHeap.insert (birthtime, thread) oldest_heap,
                  active = update_th (thread, (birthtime, deadtime, desc)) active,
                  cancelling = cancelling})
    end)


  (* Move all threads to cancelling *)
  fun kill_all () = protected_change (fn State {timeout_heap, oldest_heap, active, cancelling} =>
    let
    val active' = (map (fn (th, (tb, _, desc)) => (th, (tb, Time.now(), desc))) active)
    in ((),State {timeout_heap = timeout_heap,
                  oldest_heap = oldest_heap,
                  active = [],
                  cancelling = append active' cancelling})
    end)
    
  (* give information on running threads *)
  fun info () = protected (fn State {timeout_heap, oldest_heap, active, cancelling} =>
    let
    fun running_info (_, (birth_time, dead_time, desc)) = "Running: "
        ^ ((Int.toString o Time.toSeconds) (Time.- (Time.now(), birth_time)))
        ^ " s  --  "
        ^ ((Int.toString o Time.toSeconds) (Time.- (dead_time, Time.now())))
        ^ " s to live:\n" ^ desc
    fun cancelling_info (_, (_, dead_time, desc)) = "Trying to interrupt thread since "
        ^ (Int.toString o Time.toSeconds) (Time.- (Time.now(), dead_time))
        ^ " s:\n" ^ desc
    val running = if null active then "No ATPs running."
      else String.concatWith "\n\n" ("--- RUNNING ATPs ---" ::
      (map (fn entry => running_info entry) active))
    val interrupting = if null cancelling then ""
      else String.concatWith "\n\n" ("--- TRYING TO INTERRUPT FOLLOWING ATPs ---" ::
      (map (fn entry => cancelling_info entry) cancelling))
    in running ^ "\n" ^ interrupting end)

    
    (* thread wrapping an atp-call *)   
    
    fun atp_thread call_prover produce_answer =
      SimpleThread.fork true (fn () =>
        let
        val result = call_prover ()
        val message = case result of NONE => "Failed."
            | SOME result => "Try this command: " ^ produce_answer result
        in priority (unregister (isSome result) message (Thread.self()))
        end handle Interrupt => ()
      )

      
    (* preferences *)

    val atps = ref "e spass"
    val maximum_atps = ref 5   (* ~1 means infinite number of atps*)
    val timeout = ref 60
    val groupkilling = ref true
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

  fun kill_one () = 
    let
    val oldest = protected_change (fn (s as State {timeout_heap , oldest_heap, active, cancelling}) =>
      if ThreadHeap.is_empty oldest_heap orelse length active <= !maximum_atps orelse ! maximum_atps = ~1 then (NONE, s)
      else
      let val (_, oldest_thread) = ThreadHeap.min (oldest_heap)
      in (SOME oldest_thread, State {timeout_heap = timeout_heap,
        oldest_heap = ThreadHeap.delete_min oldest_heap,
        active = active,
        cancelling = cancelling}) end)
    in case oldest of NONE => ()
      | SOME thread => priority (unregister false "Interrupted (Maximum number of ATPs exceeded)." thread) end
      
  fun kill_oldest (State {timeout_heap, oldest_heap, active, cancelling}) =
    if length active > !maximum_atps andalso !maximum_atps > ~1
    then let val _ = kill_one () in kill_oldest (! state) end
    else ()
      
    
  (* sledghammer for first subgoal *)

  fun sledgehammer names proof_state =
    let
    val proverids = case names of
      [] => String.tokens (Symbol.is_ascii_blank o String.str) (! atps)
      | names => names
    val threads_names = map_filter (run_prover proof_state 1) proverids
    val birthtime = Time.now()
    val deadtime = Time.+ (Time.now(), Time.fromSeconds (! timeout))
    val _ = List.app (register birthtime deadtime) threads_names
      (*maximum number of atps must not exceed*)
    val _ = kill_oldest (! state)
    in () end


  (* concrete syntax *)

  local structure K = OuterKeyword and P = OuterParse in

  val _ =
    OuterSyntax.improper_command "atp_kill" "kill all managed provers" K.diag
      (Scan.succeed (Toplevel.no_timing o Toplevel.imperative kill_all));

  val _ =
    OuterSyntax.improper_command "atp_info" "print information about managed provers" K.diag
      (Scan.succeed (Toplevel.no_timing o Toplevel.imperative (priority o info)));

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
