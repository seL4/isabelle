(*  Title:      Pure/System/message_channel.ML
    Author:     Makarius

Preferably asynchronous channel for Isabelle messages.
*)

signature MESSAGE_CHANNEL =
sig
  type T
  val shutdown: T -> unit
  val message: T -> string -> Properties.T -> XML.body list -> unit
  val make: BinIO.outstream -> T
end;

structure Message_Channel: MESSAGE_CHANNEL =
struct

datatype message = Shutdown | Message of XML.body list;

datatype T = Message_Channel of {mbox: message Mailbox.T, thread: Thread.thread};

fun shutdown (Message_Channel {mbox, thread}) =
 (Mailbox.send mbox Shutdown;
  Mailbox.await_empty mbox;
  Isabelle_Thread.join thread);

fun message (Message_Channel {mbox, ...}) name raw_props chunks =
  let
    val robust_props = map (apply2 YXML.embed_controls) raw_props;
    val header = [XML.Elem ((name, robust_props), [])];
  in Mailbox.send mbox (Message (header :: chunks)) end;

fun make stream =
  let
    val mbox = Mailbox.create ();
    fun loop () = Mailbox.receive NONE mbox |> dispatch
    and dispatch [] = loop ()
      | dispatch (Shutdown :: _) = ()
      | dispatch (Message chunks :: rest) =
          (Byte_Message.write_message_yxml stream chunks; dispatch rest);
    val thread =
      Isabelle_Thread.fork {name = "message_channel", stack_limit = NONE, interrupts = false} loop;
  in Message_Channel {mbox = mbox, thread = thread} end;

end;
