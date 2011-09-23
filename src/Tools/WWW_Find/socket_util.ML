(*  Title:      Tools/WWW_Find/socket_util.ML
    Author:     Timothy Bourke, NICTA

Routines for working with sockets.  Following example 10.2 in "The
Standard-ML Basis Library" by Emden R. Gansner and John H. Reppy.
*)

signature SOCKET_UTIL =
sig
  val init_server_socket: string option -> int -> Socket.passive INetSock.stream_sock
  val make_streams: Socket.active INetSock.stream_sock -> BinIO.instream * BinIO.outstream
end;

structure Socket_Util: SOCKET_UTIL =
struct

fun init_server_socket opt_host port =
  let
    val sock = INetSock.TCP.socket ();
    val addr =
      (case opt_host of
         NONE => INetSock.any port
       | SOME host =>
           NetHostDB.getByName host
           |> the
           |> NetHostDB.addr
           |> rpair port
           |> INetSock.toAddr
           handle Option => raise Fail ("Cannot resolve hostname: " ^ host));
    val _ = Socket.bind (sock, addr);
    val _ = Socket.listen (sock, 5);
  in sock end;

fun make_streams sock =
  let
    val (haddr, port) = INetSock.fromAddr (Socket.Ctl.getSockName sock);

    val sock_name =
      implode [ NetHostDB.toString haddr, ":", string_of_int port ];

    val rd =
      BinPrimIO.RD {
        name = sock_name,
        chunkSize = Socket.Ctl.getRCVBUF sock,
        readVec = SOME (fn sz => Socket.recvVec (sock, sz)),
        readArr = SOME (fn buffer => Socket.recvArr (sock, buffer)),
        readVecNB = NONE,
        readArrNB = NONE,
        block = NONE,
        canInput = NONE,
        avail = fn () => NONE,
        getPos = NONE,
        setPos = NONE,
        endPos = NONE,
        verifyPos = NONE,
        close = fn () => Socket.close sock,
        ioDesc = NONE
      };

    val wr =
      BinPrimIO.WR {
        name = sock_name,
        chunkSize = Socket.Ctl.getSNDBUF sock,
        writeVec = SOME (fn buffer => Socket.sendVec (sock, buffer)),
        writeArr = SOME (fn buffer => Socket.sendArr (sock, buffer)),
        writeVecNB = NONE,
        writeArrNB = NONE,
        block = NONE,
        canOutput = NONE,
        getPos = NONE,
        setPos = NONE,
        endPos = NONE,
        verifyPos = NONE,
        close = fn () => Socket.close sock,
        ioDesc = NONE
      };

    val in_strm =
      BinIO.mkInstream (
        BinIO.StreamIO.mkInstream (rd, Word8Vector.fromList []));

    val out_strm =
      BinIO.mkOutstream (
        BinIO.StreamIO.mkOutstream (wr, IO.BLOCK_BUF));

    in (in_strm, out_strm) end;

end;

