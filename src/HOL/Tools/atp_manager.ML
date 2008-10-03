(*  Title:      HOL/Tools/atp_manager.ML
    ID:         $Id$
    Author:     Fabian Immler, TU Muenchen

ATP threads have to be registered here.  Threads with the same
birth-time are seen as one group.  All threads of a group are killed
when one thread of it has been successful, or after a certain time, or
when the maximum number of threads exceeds; then the oldest thread is
killed.
*)

signature PROVERS =
sig
  type T
  val get : Context.theory -> T
  val init : Context.theory -> Context.theory
  val map :
     (T -> T) ->
     Context.theory -> Context.theory
  val put : T -> Context.theory -> Context.theory
end;

signature ATP_MANAGER =
sig
  val kill_all: unit -> unit
  val info: unit -> unit
  val set_atps: string -> unit
  val set_max_atp: int -> unit
  val set_timeout: int -> unit
  val set_groupkilling: bool -> unit
  val start: unit -> unit
  val register: Time.time -> Time.time -> (Thread.thread * string) -> unit
  val unregister: bool -> unit

  structure Provers : PROVERS
  val sledgehammer: Toplevel.state -> unit
end;

structure AtpManager : ATP_MANAGER =
struct

  structure ThreadHeap = HeapFun (
  struct
    type elem = (Time.time * Thread.thread);
    fun ord ((a,_),(b,_)) = Time.compare (a, b);
  end);

  (* create global state of threadmanager *)
  val timeout_heap = ref ThreadHeap.empty
  val oldest_heap = ref ThreadHeap.empty
  (* managed threads *)
  val active = ref ([] : (Thread.thread * Time.time * Time.time * string) list)
  val cancelling = ref ([] : (Thread.thread * Time.time * Time.time * string) list)
  (* settings *)
  val atps = ref "e,spass"
  val maximum_atps = ref 5   (* ~1 means infinite number of atps*)
  val timeout = ref 60
  val groupkilling = ref true
  (* synchronizing *)
  val lock = Mutex.mutex () (* to be aquired for changing state *)
  val state_change = ConditionVar.conditionVar () (* signal when state changes *)
  (* watches over running threads and interrupts them if required *)
  val managing_thread = ref (Thread.fork (fn () => (), []))

  (* move a thread from active to cancelling
    managing_thread trys to interrupt all threads in cancelling

   call from an environment where a lock has already been aquired *)
  fun unregister_locked thread =
    let val entrys = (filter (fn (t,_,_,_) => Thread.equal (t, thread))) (! active)
    val entrys_update = map (fn (th, tb, _, desc) => (th, tb, Time.now(), desc)) entrys
    val _ = change cancelling (append entrys_update)
    val _ = change active (filter_out (fn (t,_,_,_) => Thread.equal (t, thread)))
    in () end;

  (* start a watching thread which runs forever *)
  (* must *not* be called more than once!! => problem with locks *)
  fun start () =
    let
    val new_thread = Thread.fork (fn () =>
      let
      (* never give up lock except for waiting *)
      val _ = Mutex.lock lock
      fun wait_for_next_event time =
        let
        (* wait for signal or next timeout, give up lock meanwhile *)
        val _ = ConditionVar.waitUntil (state_change, lock, time)
        (* move threads with priority less than Time.now() to cancelling *)
        fun cancelolder heap =
          if ThreadHeap.is_empty heap then heap else
          let val (mintime, minthread) = ThreadHeap.min heap
          in
            if mintime > Time.now() then heap
            else (unregister_locked minthread;
            cancelolder (ThreadHeap.delete_min heap))
          end
        val _ = change timeout_heap cancelolder
        (* try to interrupt threads that are to cancel*)
        fun interrupt t = Thread.interrupt t handle Thread _ => ()
        val _ = change cancelling (filter (fn (t,_,_,_) => Thread.isActive t))
        val _ = map (fn (t, _, _, _) => interrupt t) (! cancelling)
        (* if there are threads to cancel, send periodic interrupts *)
        (* TODO: find out what realtime-values are appropriate *)
        val next_time =
          if length (! cancelling) > 0 then
           Time.now() + Time.fromMilliseconds 300
          else if ThreadHeap.is_empty (! timeout_heap) then
            Time.now() + Time.fromSeconds 10
          else
            #1 (ThreadHeap.min (! timeout_heap))
          in
            wait_for_next_event next_time
          end
        in wait_for_next_event Time.zeroTime end,
        [Thread.InterruptState Thread.InterruptDefer])
      in managing_thread := new_thread end

  (* calling thread registers itself to be managed here with a relative timeout *)
  fun register birthtime deadtime (thread, name) =
    let
    val _ = Mutex.lock lock
    (* create the atp-managing-thread if this is the first call to register *)
    val _ = if Thread.isActive (! managing_thread) then () else start ()
    (* insertion *)
    val _ = change timeout_heap (ThreadHeap.insert (deadtime, thread))
    val _ = change oldest_heap (ThreadHeap.insert (birthtime, thread))
    val _ = change active (cons (thread, birthtime, deadtime, name))
    (*maximum number of atps must not exceed*)
    val _ = let
      fun kill_oldest () =
        let val (_, oldest_thread) = ThreadHeap.min (!oldest_heap)
        val _ = change oldest_heap (ThreadHeap.delete_min)
        in unregister_locked oldest_thread end
      in
        while ! maximum_atps > ~1 andalso length (! active) > ! maximum_atps
        do kill_oldest ()
      end
    (* state of threadmanager changed => signal *)
    val _ = ConditionVar.signal state_change
    val _ = Mutex.unlock lock
    in () end

  (* calling Thread unregisters itself from Threadmanager; thread is responsible
    to terminate after calling this method *)
  fun unregister success =
    let val _ = Mutex.lock lock
    val thread = Thread.self ()
    (* get birthtime of unregistering thread - for group-killing*)
    fun get_birthtime [] = Time.zeroTime
      | get_birthtime ((t,tb,td,desc)::actives) = if Thread.equal (thread, t)
      then tb
      else get_birthtime actives
    val birthtime = get_birthtime (! active)
    (* remove unregistering thread *)
    val _ = change active (filter_out (fn (t,_,_,_) => Thread.equal (t, thread)))
    val _ = if (! groupkilling) andalso success
      then (* remove all threads of the same group *)
      let
      val group_threads = filter (fn (_, tb, _, _) => tb = birthtime) (! active)
      val _ = change cancelling (append group_threads)
      val _ = change active (filter_out (fn (_, tb, _, _) => tb = birthtime))
      in () end
      else ()
    val _ = ConditionVar.signal state_change
    val _ = Mutex.unlock lock
    in () end;

  (* Move all threads to cancelling *)
  fun kill_all () =
    let
    val _ = Mutex.lock lock
    val _ = change active (map (fn (th, tb, _, desc) => (th, tb, Time.now(), desc)))
    val _ = change cancelling (append (! active))
    val _ = change active (fn _ => [])
    val _ = ConditionVar.signal state_change
    val _ = Mutex.unlock lock
    in () end;

  fun info () =
    let
    val _ = Mutex.lock lock
    fun running_info (_, birth_time, dead_time, desc) =
      priority ("Running: "
        ^ ((Int.toString o Time.toSeconds) (Time.now() - birth_time))
        ^ " s  --  "
        ^ ((Int.toString o Time.toSeconds) (dead_time - Time.now()))
        ^ " s to live:\n" ^ desc)
    fun cancelling_info (_, _, dead_time, desc) =
      priority ("Trying to interrupt thread since "
        ^ (Int.toString o Time.toSeconds) (Time.now() - dead_time)
        ^ " s:\n" ^ desc )
    val _ = if length (! active) = 0 then [priority "No ATPs running."]
      else (priority "--- RUNNING ATPs ---";
      map (fn entry => running_info entry) (! active))
    val _ = if length (! cancelling) = 0 then []
      else (priority "--- TRYING TO INTERRUPT FOLLOWING ATPs ---";
      map (fn entry => cancelling_info entry) (! cancelling))
    val _ = Mutex.unlock lock
    in () end;

    (* integration into ProofGeneral *)

    fun set_max_atp number = CRITICAL (fn () => maximum_atps := number);
    fun set_atps str = CRITICAL (fn () => atps := str);
    fun set_timeout time = CRITICAL (fn () => timeout := time);
    fun set_groupkilling boolean = CRITICAL (fn () => groupkilling := boolean);

    (* some settings will be accessible via Isabelle -> Settings *)
    val _ = ProofGeneralPgip.add_preference "Proof"
        {name = "ATP - Provers (e,vampire,spass)",
         descr = "Which external automatic provers (seperated by commas)",
         default = !atps,
         pgiptype = PgipTypes.Pgipstring,
         get = fn () => !atps,
         set = set_atps} handle Error => warning "Preference already exists";
    val _ = ProofGeneralPgip.add_preference "Proof"
        {name = "ATP - Maximum number",
         descr = "How many provers may run parallel",
         default = Int.toString (! maximum_atps),
         pgiptype = PgipTypes.Pgipstring,
         get = fn () => Int.toString (! maximum_atps),
         set = (fn str => let val int_opt = Int.fromString str
            val nr = if isSome int_opt then valOf int_opt else 1
         in set_max_atp nr end)} handle Error => warning "Preference already exists";
    val _ = ProofGeneralPgip.add_preference "Proof"
        {name = "ATP - Timeout",
         descr = "ATPs will be interrupted after this time (in seconds)",
         default = Int.toString (! timeout),
         pgiptype = PgipTypes.Pgipstring,
         get = fn () => Int.toString (! timeout),
         set = (fn str => let val int_opt = Int.fromString str
            val nr = if isSome int_opt then valOf int_opt else 60
         in set_timeout nr end)} handle Error => warning "Preference already exists";

  (* Additional Provers can be added as follows:
  SPASS with max_new 40 and theory_const false, timeout 60
  setup{* AtpManager.Provers.map (Symtab.update ("spass2", AtpThread.spass 40 false 60)) *}
  arbitrary prover supporting tptp-input/output
  setup{* AtpManagerProvers.map (Symtab.update ("tptp", AtpThread.tptp_prover "path/to/prover -options" 60)) *}
  *)
  structure Provers = TheoryDataFun
  (
    type T = (Toplevel.state -> (Thread.thread * string)) Symtab.table
    val empty = Symtab.empty
    val copy = I
    val extend = I
    fun merge _ = Symtab.merge (K true)
  );

  (* sledghammer: *)
  fun sledgehammer state =
    let
    val proverids = String.tokens (fn c => c = #",") (! atps)
    (* get context *)
    val (ctxt, _) = Proof.get_goal (Toplevel.proof_of state)
    val thy = ProofContext.theory_of ctxt
    (* get prover-functions *)
    val lookups = map (fn prover => Symtab.lookup (Provers.get thy) prover)
      proverids
    val filtered_calls = filter (fn call => isSome call) lookups
    val calls = map (fn some => valOf some) filtered_calls
    (* call provers *)
    val threads_names = map (fn call => call state) calls
    val birthtime = Time.now()
    val deadtime = Time.now() + (Time.fromSeconds (! timeout))
    val _ = map (register birthtime deadtime) threads_names
    in () end

  val _ =
    OuterSyntax.command "sledgehammer" "call all automatic theorem provers" OuterKeyword.diag
    (Scan.succeed (Toplevel.no_timing o Toplevel.unknown_proof o Toplevel.keep sledgehammer));
end;
