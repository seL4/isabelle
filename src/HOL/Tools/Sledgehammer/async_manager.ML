(*  Title:      HOL/Tools/Sledgehammer/async_manager.ML
    Author:     Fabian Immler, TU Muenchen
    Author:     Makarius
    Author:     Jasmin Blanchette, TU Muenchen

Central manager for asynchronous diagnosis tool threads.
*)

signature ASYNC_MANAGER =
sig
  val break_into_chunks : string -> string list
  val launch :
    string -> Time.time -> Time.time -> string * string
    -> (unit -> bool * string) -> unit
  val kill_threads : string -> string -> unit
  val has_running_threads : string -> bool
  val running_threads : string -> string -> unit
  val thread_messages : string -> string -> int option -> unit
end;

structure Async_Manager : ASYNC_MANAGER =
struct

(** preferences **)

val message_store_limit = 20
val message_display_limit = 10


(** thread management **)

fun implode_message (workers, work) =
  space_implode " " (Try.serial_commas "and" workers) ^ work


(* data structures over threads *)

structure Thread_Heap = Heap
(
  type elem = Time.time * Thread.thread
  fun ord ((a, _), (b, _)) = Time.compare (a, b)
)

fun lookup_thread xs = AList.lookup Thread.equal xs
fun delete_thread xs = AList.delete Thread.equal xs
fun update_thread xs = AList.update Thread.equal xs


(* state of thread manager *)

type state =
  {manager: Thread.thread option,
   timeout_heap: Thread_Heap.T,
   active:
     (Thread.thread
      * (string * Time.time * Time.time * (string * string))) list,
   canceling:  (Thread.thread * (string * Time.time * (string * string))) list,
   messages: (bool * (string * (string * string))) list,
   store: (string * (string * string)) list}

fun make_state manager timeout_heap active canceling messages store : state =
  {manager = manager, timeout_heap = timeout_heap, active = active,
   canceling = canceling, messages = messages, store = store}

val global_state = Synchronized.var "async_manager"
  (make_state NONE Thread_Heap.empty [] [] [] [])


(* unregister thread *)

fun unregister (urgent, message) thread =
  Synchronized.change global_state
  (fn state as {manager, timeout_heap, active, canceling, messages, store} =>
    (case lookup_thread active thread of
      SOME (tool, _, _, desc as (worker, its_desc)) =>
        let
          val active' = delete_thread thread active
          val now = Time.now ()
          val canceling' = (thread, (tool, now, desc)) :: canceling
          val message' =
            (worker, its_desc ^ (if message = "" then "" else "\n" ^ message))
          val messages' = (urgent, (tool, message')) :: messages
          val store' = (tool, message') ::
            (if length store <= message_store_limit then store
             else #1 (chop message_store_limit store))
        in make_state manager timeout_heap active' canceling' messages' store' end
    | NONE => state))


(* main manager thread -- only one may exist *)

val min_wait_time = seconds 0.3
val max_wait_time = seconds 10.0

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
val break_into_chunks = space_explode "\000" o replace_all "\n\n" "\000"

fun print_new_messages () =
  Synchronized.change_result global_state
      (fn {manager, timeout_heap, active, canceling, messages, store} =>
          messages
          |> List.partition
                 (fn (urgent, _) =>
                     (null active andalso null canceling) orelse urgent)
          ||> (fn postponed_messages =>
                  make_state manager timeout_heap active canceling
                                     postponed_messages store))
  |> map (fn (_, (tool, (worker, work))) => ((tool, work), worker))
  |> AList.group (op =)
  |> List.app (fn ((_, ""), _) => ()
                | ((tool, work), workers) =>
                  tool ^ ": " ^
                  implode_message (workers |> sort_distinct string_ord, work)
                  |> break_into_chunks
                  |> List.app Output.urgent_message)

fun check_thread_manager () = Synchronized.change global_state
  (fn state as {manager, timeout_heap, active, canceling, messages, store} =>
    if (case manager of SOME thread => Thread.isActive thread | NONE => false) then state
    else let val manager = SOME (Toplevel.thread false (fn () =>
      let
        fun time_limit timeout_heap =
          (case try Thread_Heap.min timeout_heap of
            NONE => Time.+ (Time.now (), max_wait_time)
          | SOME (time, _) => time)

        (*action: find threads whose timeout is reached, and interrupt canceling threads*)
        fun action {manager, timeout_heap, active, canceling, messages, store} =
          let val (timeout_threads, timeout_heap') =
            Thread_Heap.upto (Time.now (), Thread.self ()) timeout_heap
          in
            if null timeout_threads andalso null canceling then
              NONE
            else
              let
                val _ = List.app (Simple_Thread.interrupt_unsynchronized o #1) canceling
                val canceling' = filter (Thread.isActive o #1) canceling
                val state' = make_state manager timeout_heap' active canceling' messages store
              in SOME (map #2 timeout_threads, state') end
          end
      in
        while Synchronized.change_result global_state
          (fn state as {timeout_heap, active, canceling, messages, store, ...} =>
            if null active andalso null canceling andalso null messages
            then (false, make_state NONE timeout_heap active canceling messages store)
            else (true, state))
        do
          (Synchronized.timed_access global_state
               (SOME o time_limit o #timeout_heap) action
           |> these
           |> List.app (unregister (false, "Timed out."));
           print_new_messages ();
           (* give threads some time to respond to interrupt *)
           OS.Process.sleep min_wait_time)
      end))
    in make_state manager timeout_heap active canceling messages store end)


(* register thread *)

fun register tool birth_time death_time desc thread =
 (Synchronized.change global_state
    (fn {manager, timeout_heap, active, canceling, messages, store} =>
      let
        val timeout_heap' = Thread_Heap.insert (death_time, thread) timeout_heap
        val active' = update_thread (thread, (tool, birth_time, death_time, desc)) active
        val state' = make_state manager timeout_heap' active' canceling messages store
      in state' end);
  check_thread_manager ())


fun launch tool birth_time death_time desc f =
  (Toplevel.thread true
       (fn () =>
           let
             val self = Thread.self ()
             val _ = register tool birth_time death_time desc self
           in unregister (f ()) self end);
   ())


(** user commands **)

(* kill threads *)

fun kill_threads tool das_wort_worker = Synchronized.change global_state
  (fn {manager, timeout_heap, active, canceling, messages, store} =>
    let
      val killing =
        map_filter (fn (th, (tool', _, _, desc)) =>
                       if tool' = tool then SOME (th, (tool', Time.now (), desc))
                       else NONE) active
      val state' = make_state manager timeout_heap [] (killing @ canceling) messages store
      val _ =
        if null killing then ()
        else Output.urgent_message ("Interrupted active " ^ das_wort_worker ^ "s.")
    in state' end)


(* running threads *)

fun seconds time = string_of_int (Time.toSeconds time) ^ " s"

fun has_running_threads tool =
  exists (fn (_, (tool', _, _, _)) => tool' = tool)
         (#active (Synchronized.value global_state))

fun running_threads tool das_wort_worker =
  let
    val {active, canceling, ...} = Synchronized.value global_state
    val now = Time.now ()
    fun running_info (_, (tool', birth_time, death_time, desc)) =
      if tool' = tool then
        SOME ("Running: " ^ seconds (Time.- (now, birth_time)) ^ " -- " ^
              seconds (Time.- (death_time, now)) ^ " to live:\n" ^
              op ^ desc)
      else
        NONE
    fun canceling_info (_, (tool', death_time, desc)) =
      if tool' = tool then
        SOME ("Trying to interrupt " ^ das_wort_worker ^ " since " ^
              seconds (Time.- (now, death_time)) ^ ":\n" ^ op ^ desc)
      else
        NONE
    val running =
      case map_filter running_info active of
        [] => ["No " ^ das_wort_worker ^ "s running."]
      | ss => "Running " ^ das_wort_worker ^ "s " :: ss
    val interrupting =
      case map_filter canceling_info canceling of
        [] => []
      | ss => "Interrupting " ^ das_wort_worker ^ "s " :: ss
  in Output.urgent_message (space_implode "\n\n" (running @ interrupting)) end

fun thread_messages tool das_wort_worker opt_limit =
  let
    val limit = the_default message_display_limit opt_limit
    val tool_store = Synchronized.value global_state
                     |> #store |> filter (curry (op =) tool o fst)
    val header =
      "Recent " ^ das_wort_worker ^ " messages" ^
        (if length tool_store <= limit then ":"
         else " (" ^ string_of_int limit ^ " displayed):")
    val ss = tool_store |> chop limit |> #1 |> map (op ^ o snd)
  in List.app Output.urgent_message (header :: maps break_into_chunks ss) end

end;
