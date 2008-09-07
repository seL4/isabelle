(*  Title:      Pure/Concurrent/mailbox.ML
    ID:         $Id$
    Author:     Makarius

Concurrent message exchange via mailbox -- with unbounded queueing.
*)

signature MAILBOX =
sig
  type 'a T
  val create: unit -> 'a T
  val send: 'a -> 'a T -> unit
  val receive_timeout: Time.time -> 'a T -> 'a option
  val receive: 'a T -> 'a
end;

structure Mailbox: MAILBOX =
struct

(* datatype *)

datatype 'a T = Mailbox of
  {lock: Mutex.mutex,
   cond: ConditionVar.conditionVar,
   messages: 'a Queue.T ref};

fun create () = Mailbox
  {lock = Mutex.mutex (),
   cond = ConditionVar.conditionVar (),
   messages = ref Queue.empty};


(* send -- non-blocking *)

fun send msg (Mailbox {lock, cond, messages}) = uninterruptible (fn _ => fn () =>
  let
    val _ = Mutex.lock lock;
    val _ = change messages (Queue.enqueue msg);
    val _ = Mutex.unlock lock;
    val _ = ConditionVar.broadcast cond;
  in () end) ();


(* receive -- blocking, interruptible, with timeout *)

fun receive_timeout timeout (Mailbox {lock, cond, messages}) =
  uninterruptible (fn restore_attributes => fn () =>
    let
      val _ = Mutex.lock lock;

      val limit = Time.+ (Time.now (), timeout);
      fun check () = not (Queue.is_empty (! messages)) orelse
        ConditionVar.waitUntil (cond, lock, limit) andalso check ();
      val ok = restore_attributes check ()
        handle Interrupt => (Mutex.unlock lock; raise Interrupt);
      val res =
        if ok then
          let
            val (msg, msgs) = Queue.dequeue (! messages);
            val _ = messages := msgs;
          in SOME msg end
        else NONE;

      val _ = Mutex.unlock lock;
    in res end) ();

fun receive mailbox =
  (case receive_timeout (Time.fromSeconds 10) mailbox of
    NONE => receive mailbox
  | SOME x => x);

end;
