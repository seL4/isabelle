(*  Title:      Pure/System/message_channel.ML
    Author:     Makarius

Preferably asynchronous channel for Isabelle messages.
*)

signature MESSAGE_CHANNEL =
sig
  type T
  val send: T -> string list -> bool -> unit
  val shutdown: T -> unit
  val make: System_Channel.T -> T
end;

structure Message_Channel: MESSAGE_CHANNEL =
struct

datatype T = Message_Channel of
 {send: string list -> bool -> unit,
  shutdown: unit -> unit};

fun send (Message_Channel {send, ...}) = send;
fun shutdown (Message_Channel {shutdown, ...}) = shutdown ();

fun flush channel = ignore (try System_Channel.flush channel);

fun message_output mbox channel =
  let
    fun loop receive =
      (case receive mbox of
        SOME NONE => flush channel
      | SOME (SOME (msg, do_flush)) =>
         (List.app (fn s => System_Channel.output channel s) msg;
          if do_flush then flush channel else ();
          loop (Mailbox.receive_timeout (seconds 0.02)))
      | NONE => (flush channel; loop (SOME o Mailbox.receive)));
  in fn () => loop (SOME o Mailbox.receive) end;

fun make channel =
  if Multithreading.available then
    let
      val mbox = Mailbox.create ();
      val thread = Simple_Thread.fork false (message_output mbox channel);
      fun send msg do_flush = Mailbox.send mbox (SOME (msg, do_flush));
      fun shutdown () =
        (Mailbox.send mbox NONE; Mailbox.await_empty mbox; Simple_Thread.join thread);
    in Message_Channel {send = send, shutdown = shutdown} end
  else
    let
      fun send msg = (List.app (fn s => System_Channel.output channel s) msg; flush channel);
    in Message_Channel {send = fn msg => fn _ => send msg, shutdown = fn () => ()} end;

end;

