(*  Title:      Pure/Concurrent/event_timer.ML
    Author:     Makarius

Initiate event after given point in time.

Note: events are run as synchronized action within a dedicated thread
and should finish quickly without further ado.
*)

signature EVENT_TIMER =
sig
  type request
  val eq_request: request * request -> bool
  val request: {physical: bool} -> Time.time -> (unit -> unit) -> request
  val cancel: request -> bool
  val future: {physical: bool} -> Time.time -> unit future
  val shutdown: unit -> unit
end;

structure Event_Timer: EVENT_TIMER =
struct

(* type request *)

datatype request =
  Request of {id: int, gc_start: Time.time option, time: Time.time, event: unit -> unit};

val new_id = Counter.make ();

fun new_request physical time event =
  Request {
    id = new_id (),
    gc_start = if physical then NONE else SOME (ML_Heap.gc_now ()),
    time = time,
    event = event};

fun eq_request (Request {id = id1, ...}, Request {id = id2, ...}) = id1 = id2;

fun request_gc_start (Request {gc_start, ...}) = gc_start;
fun request_time (Request {time, ...}) = time;
fun request_event (Request {event, ...}) = event;


(* type requests *)

structure Requests = Table(type key = Time.time val ord = Time.compare);
type requests = request list Requests.table;

fun add req_time req (requests: requests) =
  Requests.cons_list (req_time, req) requests;

fun del req (requests: requests) =
  let
    val old =
      requests |> Requests.get_first (fn (key, reqs) =>
        reqs |> get_first (fn req' =>
          if eq_request (req', req) then SOME (key, req') else NONE));
  in
    (case old of
      NONE => (false, requests)
    | SOME req' => (true, Requests.remove_list eq_request req' requests))
  end;

fun next_time (requests: requests) =
  Option.map #1 (Requests.min requests);

fun next_event (now, gc_now) (requests: requests) =
  (case Requests.min requests of
    NONE => NONE
  | SOME (req_time, reqs) =>
      if now < req_time then NONE
      else
        let
          val (reqs', req) = split_last reqs;
          val requests' =
            if null reqs'
            then Requests.delete req_time requests
            else Requests.update (req_time, reqs') requests;
          val req_time' =
            (case request_gc_start req of
              NONE => req_time
            | SOME gc_start => request_time req + (gc_now - gc_start));
        in
          if now < req_time'
          then (fn () => (), add req_time' req requests')
          else (request_event req, requests')
        end |> SOME);


(* global state *)

datatype status = Normal | Shutdown_Req | Shutdown_Ack;

datatype state =
  State of {requests: requests, status: status, manager: Thread.thread option};

fun make_state (requests, status, manager) =
  State {requests = requests, status = status, manager = manager};

val normal_state = make_state (Requests.empty, Normal, NONE);
val shutdown_ack_state = make_state (Requests.empty, Shutdown_Ack, NONE);

fun is_shutdown s (State {requests, status, manager}) =
  Requests.is_empty requests andalso status = s andalso is_none manager;

fun is_shutdown_req (State {requests, status, ...}) =
  Requests.is_empty requests andalso status = Shutdown_Req;

val state = Synchronized.var "Event_Timer.state" normal_state;


(* manager thread *)

fun manager_loop () =
  if Synchronized.timed_access state
    (fn State {requests, ...} => next_time requests)
    (fn st as State {requests, status, manager} =>
      (case next_event (Time.now (), ML_Heap.gc_now ()) requests of
        SOME (event, requests') =>
          let
            val _ = Exn.capture event ();
            val state' = make_state (requests', status, manager);
          in SOME (true, state') end
      | NONE =>
          if is_shutdown_req st
          then SOME (false, shutdown_ack_state)
          else NONE)) <> SOME false
  then manager_loop () else ();

fun manager_check manager =
  if is_some manager andalso Thread.isActive (the manager) then manager
  else
    SOME (Standard_Thread.fork {name = "event_timer", stack_limit = NONE, interrupts = false}
      manager_loop);

fun shutdown () =
  Thread_Attributes.uninterruptible (fn restore_attributes => fn () =>
    if Synchronized.change_result state (fn st as State {requests, manager, ...} =>
      if is_shutdown Normal st then (false, st)
      else if is_shutdown Shutdown_Ack st orelse is_shutdown_req st then
        raise Fail "Concurrent attempt to shutdown event timer"
      else (true, make_state (requests, Shutdown_Req, manager_check manager)))
    then
      restore_attributes (fn () =>
        Synchronized.guarded_access state
          (fn st => if is_shutdown Shutdown_Ack st then SOME ((), normal_state) else NONE)) ()
      handle exn =>
        if Exn.is_interrupt exn then
          Synchronized.change state (fn State {requests, manager, ...} =>
            make_state (requests, Normal, manager))
        else ()
    else ()) ();


(* main operations *)

fun request {physical} time event =
  Synchronized.change_result state (fn State {requests, status, manager} =>
    let
      val req = new_request physical time event;
      val requests' = add time req requests;
      val manager' = manager_check manager;
    in (req, make_state (requests', status, manager')) end);

fun cancel req =
  Synchronized.change_result state (fn State {requests, status, manager} =>
    let
      val (canceled, requests') = del req requests;
      val manager' = manager_check manager;
    in (canceled, make_state (requests', status, manager')) end);

fun future physical time =
  Thread_Attributes.uninterruptible (fn _ => fn () =>
    let
      val req: request Single_Assignment.var = Single_Assignment.var "req";
      fun abort () = ignore (cancel (Single_Assignment.await req));
      val promise: unit future = Future.promise_name "event_timer" abort;
      val _ = Single_Assignment.assign req (request physical time (Future.fulfill promise));
    in promise end) ();

end;
