(*  Title:      Pure/System/message_channel.ML
    Author:     Makarius

Preferably asynchronous channel for Isabelle messages.
*)

signature MESSAGE_CHANNEL =
sig
  type message
  val message: string -> Properties.T -> string list -> message
  type T
  val send: T -> message -> unit
  val shutdown: T -> unit
  val make: System_Channel.T -> T
end;

structure Message_Channel: MESSAGE_CHANNEL =
struct

(* message *)

datatype message = Message of string list;

fun chunk ss =
  string_of_int (fold (Integer.add o size) ss 0) :: "\n" :: ss;

fun message name raw_props body =
  let
    val robust_props = map (pairself YXML.embed_controls) raw_props;
    val header = YXML.string_of (XML.Elem ((name, robust_props), []));
  in Message (chunk [header] @ chunk body) end;

fun output_message channel (Message ss) =
  List.app (System_Channel.output channel) ss;


(* channel *)

datatype T = Message_Channel of {send: message -> unit, shutdown: unit -> unit};

fun send (Message_Channel {send, ...}) = send;
fun shutdown (Message_Channel {shutdown, ...}) = shutdown ();

fun flush channel = ignore (try System_Channel.flush channel);

fun message_output mbox channel =
  let
    fun loop receive =
      (case receive mbox of
        SOME NONE => flush channel
      | SOME (SOME msg) =>
         (output_message channel msg;
          loop (Mailbox.receive_timeout (seconds 0.02)))
      | NONE => (flush channel; loop (SOME o Mailbox.receive)));
  in fn () => loop (SOME o Mailbox.receive) end;

fun make channel =
  if Multithreading.available then
    let
      val mbox = Mailbox.create ();
      val thread = Simple_Thread.fork false (message_output mbox channel);
      fun send msg = Mailbox.send mbox (SOME msg);
      fun shutdown () =
        (Mailbox.send mbox NONE; Mailbox.await_empty mbox; Simple_Thread.join thread);
    in Message_Channel {send = send, shutdown = shutdown} end
  else
    let
      fun send msg = (output_message channel msg; flush channel);
    in Message_Channel {send = send, shutdown = fn () => ()} end;

end;

