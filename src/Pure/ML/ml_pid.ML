(*  Title:      Pure/ML/ml_pid.ML
    Author:     Makarius

Native PID for ML process.
*)

signature ML_PID =
sig
  val get: unit -> int
end;

structure ML_Pid: ML_PID =
struct

\<^if_windows>\<open>
  val get =
    Foreign.buildCall0
      (Foreign.getSymbol (Foreign.loadLibrary "kernel32.dll") "GetCurrentProcessId", (), Foreign.cInt);
\<close>

\<^if_unix>\<open>
  val get = Posix.ProcEnv.getpid #> Posix.Process.pidToWord #> SysWord.toLargeInt;
\<close>

end;
