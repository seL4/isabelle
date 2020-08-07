(*  Title:      Pure/ML/ml_pid.ML
    Author:     Makarius

Native PID for ML process.
*)

signature ML_PID =
sig
  val get: unit -> int
end;

if ML_System.platform_is_windows then ML
\<open>
structure ML_Pid: ML_PID =
struct

val get =
  Foreign.buildCall0
    (Foreign.getSymbol (Foreign.loadLibrary "kernel32.dll") "GetCurrentProcessId", (), Foreign.cInt);

end;
\<close>
else ML
\<open>
structure ML_Pid: ML_PID =
struct

val get = Posix.ProcEnv.getpid #> Posix.Process.pidToWord #> SysWord.toLargeInt

end;
\<close>
