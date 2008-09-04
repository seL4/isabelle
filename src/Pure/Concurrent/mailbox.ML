(*  Title:      Pure/Concurrent/mailbox.ML
    ID:         $Id$

Concurrent message exchange via mailbox -- with unbounded queueing.
*)

signature MAILBOX =
sig
  type 'a T
  val create: unit -> 'a T
  val send: 'a -> 'a T -> unit
  val receive: 'a T -> 'a
end;

structure Mailbox: MAILBOX =
struct

datatype 'a T = Mailbox of
  {lock: Mutex.mutex,
   cond: ConditionVar.conditionVar,
   messages: 'a Queue.T ref};

fun create () = Mailbox
  {lock = Mutex.mutex (),
   cond = ConditionVar.conditionVar (),
   messages = ref Queue.empty};

fun send msg (Mailbox {lock, cond, messages}) = uninterruptible (fn _ => fn () =>
  let
    val _ = Mutex.lock lock;
    val _ = change messages (Queue.enqueue msg);
    val _ = Mutex.unlock lock;
    val _ = ConditionVar.signal cond;
  in () end) ();

fun receive (Mailbox {lock, cond, messages}) = uninterruptible (fn restore_attributes => fn () =>
  let
    val _ = Mutex.lock lock;
    fun check () = while (Queue.is_empty (! messages)) do (ConditionVar.wait (cond, lock));
    val _ = restore_attributes check () handle Interrupt => (Mutex.unlock lock; raise Interrupt);
    val (msg, msgs) = Queue.dequeue (! messages);
    val _ = messages := msgs;
    val _ = Mutex.unlock lock;
  in msg end) ();

end;
