(*  Title:      Pure/Concurrent/mailbox.ML
    ID:         $Id$
    Author:     Makarius

Message exchange via mailbox -- with unbounded queueing.
*)

signature MAILBOX =
sig
  type 'a T
  val create: unit -> 'a T
  val send: 'a T -> 'a -> unit
  val receive_timeout: Time.time -> 'a T -> 'a option
  val receive: 'a T -> 'a
end;

structure Mailbox: MAILBOX =
struct

datatype 'a T = Mailbox of 'a Queue.T Synchronized.var;
fun create () = Mailbox (Synchronized.var "mailbox" Queue.empty);

(*send -- non-blocking*)
fun send (Mailbox mailbox) msg = Synchronized.change mailbox (Queue.enqueue msg);

(*receive_timeout -- blocking, interruptible, with timeout*)
fun receive_timeout timeout (Mailbox mailbox) =
  Synchronized.guarded_change (not o Queue.is_empty) (fn _ => SOME (Time.+ (Time.now (), timeout)))
    mailbox (fn ok => fn msgs => if ok then Queue.dequeue msgs |>> SOME else (NONE, msgs));

(*receive -- blocking, interruptible*)
fun receive mailbox =
  (case receive_timeout (Time.fromSeconds 10) mailbox of
    NONE => receive mailbox
  | SOME x => x);

end;
