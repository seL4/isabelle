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

datatype message = Message of XML.body list;

fun message name raw_props chunks =
  let
    val robust_props = map (apply2 YXML.embed_controls) raw_props;
    val header = [XML.Elem ((name, robust_props), [])];
  in Message (header :: chunks) end;


(* channel *)

datatype T = Message_Channel of {send: message -> unit, shutdown: unit -> unit};

fun send (Message_Channel {send, ...}) = send;
fun shutdown (Message_Channel {shutdown, ...}) = shutdown ();

fun message_output mbox stream =
  let
    fun continue () = Mailbox.receive NONE mbox |> received
    and received [] = continue ()
      | received (NONE :: _) = ()
      | received (SOME (Message chunks) :: rest) =
          (Byte_Message.write_message_yxml stream chunks; received rest);
  in continue end;

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
