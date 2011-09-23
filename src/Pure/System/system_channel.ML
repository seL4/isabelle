(*  Title:      Pure/System/system_channel.ML
    Author:     Makarius

Portable system channel for inter-process communication, based on
named pipes or sockets.
*)

signature SYSTEM_CHANNEL =
sig
  type T
  val input_line: T -> string option
  val inputN: T -> int -> string
  val output: T -> string -> unit
  val flush: T -> unit
  val fifo_rendezvous: string -> string -> T
  val socket_rendezvous: string -> T
end;

structure System_Channel: SYSTEM_CHANNEL =
struct

datatype T = System_Channel of
 {input_line: unit -> string option,
  inputN: int -> string,
  output: string -> unit,
  flush: unit -> unit};

fun input_line (System_Channel {input_line = f, ...}) = f ();
fun inputN (System_Channel {inputN = f, ...}) n = f n;
fun output (System_Channel {output = f, ...}) s = f s;
fun flush (System_Channel {flush = f, ...}) = f ();


(* named pipes *)

fun fifo_rendezvous fifo1 fifo2 =
  let
    val in_stream = TextIO.openIn fifo1;
    val out_stream = TextIO.openOut fifo2;
    val _ = TextIO.StreamIO.setBufferMode (TextIO.getOutstream out_stream, IO.BLOCK_BUF);
  in
    System_Channel
     {input_line = fn () => TextIO.inputLine in_stream,
      inputN = fn n => TextIO.inputN (in_stream, n),
      output = fn s => TextIO.output (out_stream, s),
      flush = fn () => TextIO.flushOut out_stream}
  end;


(* sockets *)  (* FIXME raw unbuffered IO !?!? *)

local

fun readN socket n =
  let
    fun read i buf =
      let
        val s = Byte.bytesToString (Socket.recvVec (socket, n - i));
        val m = size s;
        val i' = i + m;
        val buf' = Buffer.add s buf;
      in if m > 0 andalso n > i' then read i' buf' else Buffer.content buf' end;
  in read 0 Buffer.empty end;

fun read_line socket =
  let
    fun result cs = implode (rev ("\n" :: cs));
    fun read cs =
      (case readN socket 1 of
        "" => if null cs then NONE else SOME (result cs)
      | "\n" => SOME (result cs)
      | c => read (c :: cs));
  in read [] end;

fun write socket =
  let
    fun send buf =
      if Word8VectorSlice.isEmpty buf then ()
      else
        let
          val n = Int.min (Word8VectorSlice.length buf, 4096);
          val m = Socket.sendVec (socket, Word8VectorSlice.subslice (buf, 0, SOME n));
          val buf' = Word8VectorSlice.subslice (buf, m, NONE);
        in send buf' end;
  in fn s => send (Word8VectorSlice.full (Byte.stringToBytes s)) end;

in

fun socket_rendezvous name =
  let
    fun err () = error ("Bad socket name: " ^ quote name);
    val (host, port) =
      (case space_explode ":" name of
        [h, p] =>
         (case NetHostDB.getByName h of SOME host => host | NONE => err (),
          case Int.fromString p of SOME port => port | NONE => err ())
      | _ => err ());
    val socket: Socket.active INetSock.stream_sock = INetSock.TCP.socket ();
    val _ = Socket.connect (socket, INetSock.toAddr (NetHostDB.addr host, port));
  in
    System_Channel
     {input_line = fn () => read_line socket,
      inputN = fn n => readN socket n,
      output = fn s => write socket s,
      flush = fn () => ()}
  end;

end;

end;

