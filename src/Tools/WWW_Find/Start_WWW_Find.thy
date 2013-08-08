(* Load this theory to start the WWW_Find server on port defined by environment
   variable "SCGIPORT". Used by the isabelle wwwfind tool.
*)

theory Start_WWW_Find imports WWW_Find begin

ML {*
  val port = Markup.parse_int (getenv "SCGIPORT");
  ScgiServer.server' 10 "/" port;
*}

end

