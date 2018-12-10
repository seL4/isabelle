(*  Title:      Pure/System/system_channel.ML
    Author:     Makarius

Socket-based system channel for inter-process communication.
*)

signature SYSTEM_CHANNEL =
sig
  type T
  val input_line: T -> string option
  val inputN: T -> int -> string
  val output: T -> string -> unit
  val flush: T -> unit
  val rendezvous: string -> T
end;

structure System_Channel: SYSTEM_CHANNEL =
struct

datatype T = System_Channel of BinIO.instream * BinIO.outstream;

fun input_line (System_Channel (stream, _)) = Bytes.read_line stream;
fun inputN (System_Channel (stream, _)) n = Bytes.read_block stream n;

fun output (System_Channel (_, stream)) s = File.output stream s;
fun flush (System_Channel (_, stream)) = BinIO.flushOut stream;

fun rendezvous name =
  let
    val (in_stream, out_stream) = Socket_IO.open_streams name;
    val _ = BinIO.StreamIO.setBufferMode (BinIO.getOutstream out_stream, IO.BLOCK_BUF);
  in System_Channel (in_stream, out_stream) end;

end;
