(*  Title:      Tools/WWW_Find/echo.ML
    Author:     Timothy Bourke, NICTA

Install simple echo server.
*)

local
fun echo (req, content, send) =
  (send (ScgiReq.show req);
   send "--payload-----\n";
   send (Byte.bytesToString content);
   send "\n--------------\n")
in
val () = ScgiServer.register ("echo", SOME Mime.plain, echo);
end;

