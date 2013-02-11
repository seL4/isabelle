(* Load this theory to start the WWW_Find server on port defined by environment
   variable "SCGIPORT". Used by the isabelle wwwfind tool.
*)

theory Start_WWW_Find imports WWW_Find begin

ML {*
  YXML_Find_Theorems.init ();
  val port = OS.Process.getEnv "SCGIPORT" |> the |> Int.fromString |> the;
  ScgiServer.server' 10 "/" port;
*}

end

