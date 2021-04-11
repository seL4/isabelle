(*  Title:      Pure/System/message_channel.ML
    Author:     Makarius

Preferably asynchronous channel for Isabelle messages.
*)

signature MESSAGE_CHANNEL =
sig
  type message
  val message: string -> Properties.T -> XML.body list -> message
  type T
  val send: T -> message -> unit
  val shutdown: T -> unit
  val make: BinIO.outstream -> T
end;

structure Message_Channel: MESSAGE_CHANNEL =
struct

(* message *)

datatype message = Message of {chunks: XML.body list, flush: bool};

fun message name raw_props chunks =
  let
    val robust_props = map (apply2 YXML.embed_controls) raw_props;
    val header = [XML.Elem ((name, robust_props), [])];
  in Message {chunks = header :: chunks, flush = name = Markup.protocolN} end;


(* channel *)

datatype T = Message_Channel of {send: message -> unit, shutdown: unit -> unit};

fun send (Message_Channel {send, ...}) = send;
fun shutdown (Message_Channel {shutdown, ...}) = shutdown ();

val flush_timeout = SOME (seconds 0.02);

fun message_output mbox stream =
  let
    fun continue timeout =
      (case Mailbox.receive timeout mbox of
        [] => (Byte_Message.flush stream; continue NONE)
      | msgs => received timeout msgs)
    and received _ (NONE :: _) = Byte_Message.flush stream
      | received _ (SOME (Message {chunks, flush}) :: rest) =
          let
            val _ = Byte_Message.write_message_yxml stream chunks;
            val timeout = if flush then (Byte_Message.flush stream; NONE) else flush_timeout;
          in received timeout rest end
      | received timeout [] = continue timeout;
  in fn () => continue NONE end;

fun make stream =
  let
    val mbox = Mailbox.create ();
    val thread =
      Isabelle_Thread.fork {name = "channel", stack_limit = NONE, interrupts = false}
        (message_output mbox stream);
    fun send msg = Mailbox.send mbox (SOME msg);
    fun shutdown () =
      (Mailbox.send mbox NONE; Mailbox.await_empty mbox; Isabelle_Thread.join thread);
  in Message_Channel {send = send, shutdown = shutdown} end;

end;
