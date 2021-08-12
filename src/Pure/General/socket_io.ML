(*  Title:      Pure/General/socket_io.ML
    Author:     Timothy Bourke, NICTA
    Author:     Makarius

Stream IO over TCP sockets.  Following example 10.2 in "The Standard
ML Basis Library" by Emden R. Gansner and John H. Reppy.
*)

signature SOCKET_IO =
sig
  val make_streams: Socket.active INetSock.stream_sock -> BinIO.instream * BinIO.outstream
  val open_streams: string -> BinIO.instream * BinIO.outstream
  val with_streams: (BinIO.instream * BinIO.outstream -> 'a) -> string -> 'a
  val with_streams': (BinIO.instream * BinIO.outstream -> 'a) -> string -> string -> 'a
end;

structure Socket_IO: SOCKET_IO =
struct

fun close_permissive socket =
  Socket.close socket handle OS.SysErr _ => ();

fun make_streams socket =
  let
    val (host, port) = INetSock.fromAddr (Socket.Ctl.getSockName socket);
    val name = NetHostDB.toString host ^ ":" ^ string_of_int port;

    val rd =
      BinPrimIO.RD {
        name = name,
        chunkSize = 4096,
        readVec = SOME (fn n => Socket.recvVec (socket, n)),
        readArr = SOME (fn buffer => Socket.recvArr (socket, buffer)),
        readVecNB = NONE,
        readArrNB = NONE,
        block = NONE,
        canInput = NONE,
        avail = fn () => NONE,
        getPos = NONE,
        setPos = NONE,
        endPos = NONE,
        verifyPos = NONE,
        close = fn () => close_permissive socket,
        ioDesc = NONE
      };

    val wr =
      BinPrimIO.WR {
        name = name,
        chunkSize = 4096,
        writeVec = SOME (fn buffer => Socket.sendVec (socket, buffer)),
        writeArr = SOME (fn buffer => Socket.sendArr (socket, buffer)),
        writeVecNB = NONE,
        writeArrNB = NONE,
        block = NONE,
        canOutput = NONE,
        getPos = NONE,
        setPos = NONE,
        endPos = NONE,
        verifyPos = NONE,
        close = fn () => close_permissive socket,
        ioDesc = NONE
      };

    val in_stream =
      BinIO.mkInstream
        (BinIO.StreamIO.mkInstream (rd, Word8Vector.fromList []));

    val out_stream =
      BinIO.mkOutstream
        (BinIO.StreamIO.mkOutstream (wr, IO.BLOCK_BUF));

  in (in_stream, out_stream) end;


fun open_streams socket_name =
  let
    fun err () = error ("Bad socket name: " ^ quote socket_name);
    val (host, port) =
      (case space_explode ":" socket_name of
        [h, p] =>
         (case NetHostDB.getByName h of SOME host => host | NONE => err (),
          case Int.fromString p of SOME port => port | NONE => err ())
      | _ => err ());
    val socket: Socket.active INetSock.stream_sock = INetSock.TCP.socket ();
    val _ = Socket.connect (socket, INetSock.toAddr (NetHostDB.addr host, port));
  in make_streams socket end
  handle OS.SysErr (msg, _) => error (msg ^ ": failed to open socket " ^ socket_name);

fun with_streams f =
  Thread_Attributes.uninterruptible (fn restore_attributes => fn socket_name =>
    let
      val streams = open_streams socket_name;
      val result = Exn.capture (restore_attributes f) streams;
    in BinIO.closeIn (#1 streams); BinIO.closeOut (#2 streams); Exn.release result end);

fun with_streams' f socket_name password =
  with_streams (fn streams =>
    (Byte_Message.write_line (#2 streams) password; f streams)) socket_name;

end;
