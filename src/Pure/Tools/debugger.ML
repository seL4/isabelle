(*  Title:      Pure/Tools/debugger.ML
    Author:     Makarius

Interactive debugger for Isabelle/ML.
*)

signature DEBUGGER =
sig
end;

structure Debugger: DEBUGGER =
struct

val _ = Session.protocol_handler "isabelle.Debugger$Handler";

end;
