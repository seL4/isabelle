(*  Title:      HOL/Tools/ATP_Manager/async_manager.ML
    Author:     Fabian Immler, TU Muenchen
    Author:     Makarius
    Author:     Jasmin Blanchette, TU Muenchen

Central manager for asynchronous diagnosis tool threads.
*)

signature ASYNC_MANAGER =
sig
  val unregister : bool -> string -> Thread.thread -> unit
  val register :
    string -> bool -> Time.time -> Time.time -> Thread.thread * string -> unit
  val kill_threads : string -> unit
  val running_threads : string -> unit
  val thread_messages : string -> int option -> unit
end;

structure Async_Manager : ASYNC_MANAGER =
struct

(** preferences **)

val message_store_limit = 20;
val message_display_limit = 5;


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
  canceling: (Thread.thread * (Time.time * string)) list,
  messages: string list,
  store: string list};

fun make_state manager timeout_heap active canceling messages store : state =
  {manager = manager, timeout_heap = timeout_heap, active = active,
   canceling = canceling, messages = messages, store = store}

val global_state = Synchronized.var "async_manager"
  (make_state NONE Thread_Heap.empty [] [] [] []);


(* unregister thread *)

fun unregister verbose message thread =
  Synchronized.change global_state
  (fn state as {manager, timeout_heap, active, canceling, messages, store} =>
    (case lookup_thread active thread of
      SOME (birth_time, _, desc) =>
        let
          val active' = delete_thread thread active;
          val now = Time.now ()
          val canceling' = (thread, (now, desc)) :: canceling
          val message' =
            desc ^ "\n" ^ message ^
            (if verbose then
               "Total time: " ^ Int.toString (Time.toMilliseconds
                                          (Time.- (now, birth_time))) ^ " ms.\n"
             else
               "")
          val messages' = message' :: messages;
          val store' = message' ::
            (if length store <= message_store_limit then store
             else #1 (chop message_store_limit store));
        in make_state manager timeout_heap active' canceling' messages' store' end
    | NONE => state));


(* main manager thread -- only one may exist *)

val min_wait_time = Time.fromMilliseconds 300;
val max_wait_time = Time.fromSeconds 10;

fun replace_all bef aft =
  let
    fun aux seen "" = String.implode (rev seen)
      | aux seen s =
        if String.isPrefix bef s then
          aux seen "" ^ aft ^ aux [] (unprefix bef s)
        else
          aux (String.sub (s, 0) :: seen) (String.extract (s, 1, NONE))
  in aux [] end

(* This is a workaround for Proof General's off-by-a-few sendback display bug,
   whereby "pr" in "proof" is not highlighted. *)
val break_into_chunks =
  map (replace_all "\n\n" "\000") #> maps (space_explode "\000")

fun print_new_messages tool =
  case Synchronized.change_result global_state
         (fn {manager, timeout_heap, active, canceling, messages, store} =>
             (messages, make_state manager timeout_heap active canceling []
                                   store)) of
    [] => ()
  | msgs =>
    msgs |> break_into_chunks
         |> (fn msg :: msgs => tool ^ ": " ^ msg :: msgs)
         |> List.app priority

fun check_thread_manager tool verbose = Synchronized.change global_state
  (fn state as {manager, timeout_heap, active, canceling, messages, store} =>
    if (case manager of SOME thread => Thread.isActive thread | NONE => false) then state
    else let val manager = SOME (Toplevel.thread false (fn () =>
      let
        fun time_limit timeout_heap =
          (case try Thread_Heap.min timeout_heap of
            NONE => Time.+ (Time.now (), max_wait_time)
          | SOME (time, _) => time);

        (*action: find threads whose timeout is reached, and interrupt canceling threads*)
        fun action {manager, timeout_heap, active, canceling, messages, store} =
          let val (timeout_threads, timeout_heap') =
            Thread_Heap.upto (Time.now (), Thread.self ()) timeout_heap;
          in
            if null timeout_threads andalso null canceling
            then NONE
            else
              let
                val _ = List.app (Simple_Thread.interrupt o #1) canceling
                val canceling' = filter (Thread.isActive o #1) canceling
                val state' = make_state manager timeout_heap' active canceling' messages store;
              in SOME (map #2 timeout_threads, state') end
          end;
      in
        while Synchronized.change_result global_state
          (fn state as {timeout_heap, active, canceling, messages, store, ...} =>
            if null active andalso null canceling andalso null messages
            then (false, make_state NONE timeout_heap active canceling messages store)
            else (true, state))
        do
          (Synchronized.timed_access global_state (SOME o time_limit o #timeout_heap) action
            |> these
            |> List.app (unregister verbose "Timed out.\n");
            print_new_messages tool;
            (*give threads some time to respond to interrupt*)
            OS.Process.sleep min_wait_time)
      end))
    in make_state manager timeout_heap active canceling messages store end)


(* register thread *)

fun register tool verbose birth_time death_time (thread, desc) =
 (Synchronized.change global_state
    (fn {manager, timeout_heap, active, canceling, messages, store} =>
      let
        val timeout_heap' = Thread_Heap.insert (death_time, thread) timeout_heap;
        val active' = update_thread (thread, (birth_time, death_time, desc)) active;
        val state' = make_state manager timeout_heap' active' canceling messages store;
      in state' end);
  check_thread_manager tool verbose);



(** user commands **)

(* kill threads *)

fun kill_threads tools = Synchronized.change global_state
  (fn {manager, timeout_heap, active, canceling, messages, store} =>
    let
      val killing = map (fn (th, (_, _, desc)) => (th, (Time.now (), desc))) active;
      val state' = make_state manager timeout_heap [] (killing @ canceling) messages store;
      val _ = if null active then () else priority ("Killed active " ^ tools ^ ".")
    in state' end);


(* running threads *)

fun seconds time = string_of_int (Time.toSeconds time) ^ "s";

fun running_threads tools =
  let
    val {active, canceling, ...} = Synchronized.value global_state;

    val now = Time.now ();
    fun running_info (_, (birth_time, death_time, desc)) =
      "Running: " ^ seconds (Time.- (now, birth_time)) ^ " -- " ^
        seconds (Time.- (death_time, now)) ^ " to live:\n" ^ desc;
    fun canceling_info (_, (deadth_time, desc)) =
      "Trying to interrupt thread since " ^ seconds (Time.- (now, deadth_time)) ^ ":\n" ^ desc;

    val running =
      case map running_info active of
        [] => ["No " ^ tools ^ " running."]
      | ss => "Running " ^ tools ^ ":" :: ss
    val interrupting =
      case map canceling_info canceling of
        [] => []
      | ss => "Trying to interrupt the following " ^ tools ^ ":" :: ss
  in priority (space_implode "\n\n" (running @ interrupting)) end

fun thread_messages tool opt_limit =
  let
    val limit = the_default message_display_limit opt_limit;
    val {store, ...} = Synchronized.value global_state;
    val header =
      "Recent " ^ tool ^ " messages" ^
        (if length store <= limit then ":" else " (" ^ string_of_int limit ^ " displayed):");
  in List.app priority (header :: break_into_chunks (#1 (chop limit store))) end

end;
