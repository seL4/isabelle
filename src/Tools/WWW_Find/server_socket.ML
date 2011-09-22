(*  Title:      Tools/WWW_Find/socket_util.ML
    Author:     Timothy Bourke, NICTA

Server sockets.
*)

signature SERVER_SOCKET =
sig
  val init: string option -> int -> Socket.passive INetSock.stream_sock
end;

structure Server_Socket: SERVER_SOCKET =
struct

fun init opt_host port =
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

end;

