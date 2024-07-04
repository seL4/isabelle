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

datatype T = Message_Channel of {mbox: message Mailbox.T, thread: Isabelle_Thread.T};

fun shutdown (Message_Channel {mbox, thread}) =
 (Mailbox.send mbox Shutdown;
  Mailbox.await_empty mbox;
  Isabelle_Thread.join thread);

fun message (Message_Channel {mbox, ...}) name props chunks =
  let
    val kind = XML.Encode.string name;
    val props_length = XML.Encode.int (length props);
    val props_chunks = map (XML.Encode.string o Properties.print_eq) props;
  in Mailbox.send mbox (Message (kind :: props_length :: props_chunks @ chunks)) end;

fun make stream =
  let
    val mbox = Mailbox.create ();
    fun loop () = Mailbox.receive NONE mbox |> dispatch
    and dispatch [] = loop ()
      | dispatch (Shutdown :: _) = ()
      | dispatch (Message chunks :: rest) =
          (Byte_Message.write_message_yxml stream chunks; dispatch rest);
    val thread = Isabelle_Thread.fork (Isabelle_Thread.params "message_channel") loop;
  in Message_Channel {mbox = mbox, thread = thread} end;

end;
