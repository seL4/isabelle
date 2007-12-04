(*  Title:      Pure/Tools/isabelle_process.ML
    ID:         $Id$
    Author:     Makarius

Isabelle process wrapper -- interaction via external program.
*)

signature ISABELLE_PROCESS =
sig
  val init: unit -> unit
end;

structure IsabelleProcess: ISABELLE_PROCESS =
struct

fun init () =
  (Output.writeln_default ("ML_PID=" ^ string_of_pid (Posix.ProcEnv.getpid ()));
  Isar.secure_main ());

end;

