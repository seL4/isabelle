(*  Title:      HOL/Tools/Sledgehammer/async_manager_legacy.ML
    Author:     Fabian Immler, TU Muenchen
    Author:     Makarius
    Author:     Jasmin Blanchette, TU Muenchen

Central manager for asynchronous diagnosis tool threads.

Proof General legacy!
*)

signature ASYNC_MANAGER_LEGACY =
sig
  val thread : string -> Time.time -> Time.time -> string * string -> (unit -> bool * string) ->
    unit
  val has_running_threads : string -> bool
end;

structure Async_Manager_Legacy : ASYNC_MANAGER_LEGACY =
struct

fun implode_message (workers, work) =
  implode_space (Try.serial_commas "and" workers) ^ work

structure Thread_Heap = Heap
(
  type elem = Time.time * Isabelle_Thread.T
  fun ord ((a, _), (b, _)) = Time.compare (a, b)
)

fun lookup_thread xs = AList.lookup Isabelle_Thread.equal xs
fun delete_thread xs = AList.delete Isabelle_Thread.equal xs
fun update_thread xs = AList.update Isabelle_Thread.equal xs

type state =
  {manager: Isabelle_Thread.T option,
   timeout_heap: Thread_Heap.T,
   active:
     (Isabelle_Thread.T
      * (string * Time.time * Time.time * (string * string))) list,
   canceling:  (Isabelle_Thread.T * (string * Time.time * (string * string))) list,
   messages: (bool * (string * (string * string))) list}

fun make_state manager timeout_heap active canceling messages : state =
  {manager = manager, timeout_heap = timeout_heap, active = active, canceling = canceling,
   messages = messages}

val global_state = Synchronized.var "async_manager" (make_state NONE Thread_Heap.empty [] [] [])

fun unregister (urgent, message) thread =
  Synchronized.change global_state
  (fn state as {manager, timeout_heap, active, canceling, messages} =>
    (case lookup_thread active thread of
      SOME (tool, _, _, desc as (worker, its_desc)) =>
        let
          val active' = delete_thread thread active
          val now = Time.now ()
          val canceling' = (thread, (tool, now, desc)) :: canceling
          val message' =
            (worker, its_desc ^ (if message = "" then "" else "\n" ^ message))
          val messages' = (urgent, (tool, message')) :: messages
        in make_state manager timeout_heap active' canceling' messages' end
    | NONE => state))

val min_wait_time = seconds 0.3
val max_wait_time = seconds 10.0

fun print_new_messages () =
  Synchronized.change_result global_state
      (fn {manager, timeout_heap, active, canceling, messages} =>
          messages
          |> List.partition
                 (fn (urgent, _) =>
                     (null active andalso null canceling) orelse urgent)
          ||> make_state manager timeout_heap active canceling)
  |> map (fn (_, (tool, (worker, work))) => ((tool, work), worker))
  |> AList.group (op =)
  |> List.app (fn ((_, ""), _) => ()
                | ((tool, work), workers) =>
                  tool ^ ": " ^
                  implode_message (workers |> sort_distinct string_ord, work)
                  |> writeln)

fun check_thread_manager () = Synchronized.change global_state
  (fn state as {manager, timeout_heap, active, canceling, messages} =>
    if (case manager of SOME thread => Isabelle_Thread.is_active thread | NONE => false) then state
    else let val manager = SOME (Isabelle_Thread.fork (Isabelle_Thread.params "async_manager") (fn () =>
      let
        fun time_limit timeout_heap =
          (case try Thread_Heap.min timeout_heap of
            NONE => Time.now () + max_wait_time
          | SOME (time, _) => time)

        (*action: find threads whose timeout is reached, and interrupt canceling threads*)
        fun action {manager, timeout_heap, active, canceling, messages} =
          let val (timeout_threads, timeout_heap') =
            Thread_Heap.upto (Time.now (), Isabelle_Thread.self ()) timeout_heap
          in
            if null timeout_threads andalso null canceling then
              NONE
            else
              let
                val _ = List.app (Isabelle_Thread.interrupt_thread o #1) canceling
                val canceling' = filter (Isabelle_Thread.is_active o #1) canceling
                val state' = make_state manager timeout_heap' active canceling' messages
              in SOME (map #2 timeout_threads, state') end
          end
      in
        while Synchronized.change_result global_state
          (fn state as {timeout_heap, active, canceling, messages, ...} =>
            if null active andalso null canceling andalso null messages
            then (false, make_state NONE timeout_heap active canceling messages)
            else (true, state))
        do
          (Synchronized.timed_access global_state
               (SOME o time_limit o #timeout_heap) action
           |> these
           |> List.app (unregister (false, "Timed out"));
           print_new_messages ();
           (* give threads some time to respond to interrupt *)
           OS.Process.sleep min_wait_time)
      end))
    in make_state manager timeout_heap active canceling messages end)

fun register tool birth_time death_time desc thread =
 (Synchronized.change global_state
    (fn {manager, timeout_heap, active, canceling, messages} =>
      let
        val timeout_heap' = Thread_Heap.insert (death_time, thread) timeout_heap
        val active' = update_thread (thread, (tool, birth_time, death_time, desc)) active
        val state' = make_state manager timeout_heap' active' canceling messages
      in state' end);
  check_thread_manager ())

fun thread tool birth_time death_time desc f =
  (Isabelle_Thread.fork (Isabelle_Thread.params "async_worker" |> Isabelle_Thread.interrupts)
       (fn () =>
           let
             val self = Isabelle_Thread.self ()
             val _ = register tool birth_time death_time desc self
           in unregister (f ()) self end);
   ())

fun has_running_threads tool =
  exists (fn (_, (tool', _, _, _)) => tool' = tool) (#active (Synchronized.value global_state))

end;
