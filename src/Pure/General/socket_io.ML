(*  Title:      Pure/General/socket_io.ML
    Author:     Timothy Bourke, NICTA
    Author:     Makarius

Stream IO over TCP sockets.  Following example 10.2 in "The Standard
ML Basis Library" by Emden R. Gansner and John H. Reppy.
*)

signature SOCKET_IO =
sig
  val open_streams: string -> BinIO.instream * BinIO.outstream
  val with_streams: (BinIO.instream * BinIO.outstream -> 'a) -> string -> 'a
  val with_streams': (BinIO.instream * BinIO.outstream -> 'a) -> string -> string -> 'a
end;

structure Socket_IO: SOCKET_IO =
struct

fun close_permissive socket =
  Socket.close socket handle OS.SysErr _ => ();

val buffer_size = 65536;

fun make_streams socket_name socket =
  let
    val rd =
      BinPrimIO.RD {
        name = socket_name,
        chunkSize = buffer_size,
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
        name = socket_name,
        chunkSize = buffer_size,
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

fun socket_name_inet name =
  (case space_explode ":" name of
    [h, p] =>
     (case (NetHostDB.getByName h, Int.fromString p) of
       (SOME host, SOME port) => SOME (host, port)
     | _ => NONE)
  | _ => NONE);

fun open_streams_inet (host, port) =
  let
    val socket: Socket.active INetSock.stream_sock = INetSock.TCP.socket ();
    val _ = Socket.connect (socket, INetSock.toAddr (NetHostDB.addr host, port));

    val (socket_host, socket_port) = INetSock.fromAddr (Socket.Ctl.getSockName socket);
    val socket_name = NetHostDB.toString socket_host ^ ":" ^ string_of_int socket_port;
  in make_streams socket_name socket end;

fun open_streams_unix path =
  \<^if_windows>\<open>raise Fail "Cannot create Unix-domain socket on Windows"\<close>
  \<^if_unix>\<open>
    let
      val socket_name = File.platform_path path;
      val socket: Socket.active UnixSock.stream_sock = UnixSock.Strm.socket ();
      val _ = Socket.connect (socket, UnixSock.toAddr socket_name);
    in make_streams socket_name socket end\<close>

fun open_streams name =
  (case socket_name_inet name of
    SOME inet => open_streams_inet inet
  | NONE =>
    (case try Path.explode name of
      SOME path => open_streams_unix path
    | NONE => error ("Bad socket name: " ^ quote name)))
  handle OS.SysErr (msg, _) => error (msg ^ ": failed to open socket " ^ name);

fun with_streams f =
  Thread_Attributes.uninterruptible (fn run => fn name =>
    let
      val streams = open_streams name;
      val result = Exn.capture (run f) streams;
      val _ = BinIO.closeIn (#1 streams);
      val _ = BinIO.closeOut (#2 streams);
    in Exn.release result end);

fun with_streams' f name password =
  with_streams (fn streams =>
    (Byte_Message.write_line (#2 streams) (Bytes.string password); f streams)) name;

end;
