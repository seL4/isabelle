(*  Title:      Tools/WWW_Find/socket_util.ML
    Author:     Emden R. Gansner and John H. Reppy
                SML Basis Library, section 10

Routines for working with sockets.
*)

signature SOCKET_UTIL =
sig
  val init_server_socket : string option -> int ->
                           Socket.passive INetSock.stream_sock

  val make_streams : Socket.active INetSock.stream_sock
                     -> BinIO.instream * BinIO.outstream
end;

structure SocketUtil =
struct

fun init_server_socket hosto port =
  let
    val sock = INetSock.TCP.socket ();
    val addr =
      (case hosto of
         NONE => INetSock.any port
       | SOME host =>
           NetHostDB.getByName host
           |> the
           |> NetHostDB.addr
           |> rpair port
           |> INetSock.toAddr
           handle Option => raise Fail ("Cannot resolve hostname: " ^ host));
  in
    Socket.bind (sock, addr);
    Socket.listen (sock, 5);
    sock
  end;

fun make_streams sock =
  let
    val (haddr, port) = INetSock.fromAddr (Socket.Ctl.getSockName sock);

    val sock_name =
      String.concat [ NetHostDB.toString haddr, ":", Int.toString port ];

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

