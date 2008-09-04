(*  Title:      Pure/Concurrent/schedule.ML
    ID:         $Id$

Scheduling -- multiple threads working on a queue of tasks.
*)

signature SCHEDULE =
sig
  datatype 'a task =
    Task of {body: unit -> unit, cont: 'a -> 'a, fail: 'a -> 'a} | Wait | Terminate;
  val schedule: int -> ('a -> 'a task * 'a) -> 'a -> exn list
end;

structure Schedule: SCHEDULE =
struct

datatype 'a task =
  Task of {body: unit -> unit, cont: 'a -> 'a, fail: 'a -> 'a} | Wait | Terminate;

fun schedule n next_task = uninterruptible (fn restore_attributes => fn tasks =>
  let
    (*protected execution*)
    val lock = Mutex.mutex ();
    fun PROTECTED e =
      let
        val _ = Mutex.lock lock;
        val res = Exn.capture e ();
        val _ = Mutex.unlock lock;
      in Exn.release res end;

    (*wakeup condition*)
    val wakeup = ConditionVar.conditionVar ();
    fun wakeup_all () = ConditionVar.broadcast wakeup;
    fun wait () = ConditionVar.wait (wakeup, lock);
    fun wait_timeout () =
      ConditionVar.waitUntil (wakeup, lock, Time.+ (Time.now (), Time.fromSeconds 1));

    (*queue of tasks*)
    val queue = ref tasks;
    val active = ref 0;
    fun trace_active () = Multithreading.tracing 1 (fn () =>
      "SCHEDULE: " ^ string_of_int (! active) ^ " active");
    fun dequeue () =
      let
        val (next, tasks') = next_task (! queue);
        val _ = queue := tasks';
      in
        (case next of Wait =>
          (dec active; trace_active ();
            wait ();
            inc active; trace_active ();
            dequeue ())
        | _ => next)
      end;

    (*pool of running threads*)
    val status = ref ([]: exn list);
    val running = ref ([]: Thread.thread list);
    fun start f =
      (inc active;
       change running (cons (Thread.fork (f, [Thread.InterruptState Thread.InterruptDefer]))));
    fun stop () =
      (dec active;
       change running (filter (fn t => not (Thread.equal (t, Thread.self ())))));

    (*worker thread*)
    fun worker () =
      (case PROTECTED dequeue of
        Task {body, cont, fail} =>
          (case Exn.capture (restore_attributes body) () of
            Exn.Result () =>
              (PROTECTED (fn () => (change queue cont; wakeup_all ())); worker ())
          | Exn.Exn exn =>
              PROTECTED (fn () =>
                (change status (cons exn); change queue fail; stop (); wakeup_all ())))
      | Terminate => PROTECTED (fn () => (stop (); wakeup_all ())));

    (*main control: fork and wait*)
    fun fork 0 = ()
      | fork k = (start worker; fork (k - 1));
    val _ = PROTECTED (fn () =>
     (fork (Int.max (n, 1));
      while not (null (! running)) do
      (trace_active ();
       if not (null (! status))
       then (List.app (fn t => Thread.interrupt t handle Thread _ => ()) (! running))
       else ();
       wait_timeout ())));

  in ! status end);

end;
