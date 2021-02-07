(*  Title:      Pure/System/kill.ML
    Author:     Makarius

Kill external process group.
*)

signature KILL =
sig
  type signal
  val SIGNONE: signal
  val SIGINT: signal
  val SIGTERM: signal
  val SIGKILL: signal
  val kill_group: int -> signal -> bool
end;

if ML_System.platform_is_windows then ML
\<open>
structure Kill: KILL =
struct

type signal = string;

val SIGNONE = "0";
val SIGINT = "INT";
val SIGTERM = "TERM";
val SIGKILL = "KILL";

fun kill_group pid s =
  let
    val cmd = getenv_strict "CYGWIN_ROOT" ^ "\\bin\\bash.exe";
    val arg = "kill -" ^ s ^ " -" ^ string_of_int pid;
  in
    OS.Process.isSuccess (Windows.simpleExecute ("", quote cmd ^ " -c " ^ quote arg))
      handle OS.SysErr _ => false
  end;

end;
\<close>
else ML
\<open>
structure Kill: KILL =
struct

type signal = Posix.Signal.signal;

val SIGNONE = Posix.Signal.fromWord 0w0;
val SIGINT = Posix.Signal.int;
val SIGTERM = Posix.Signal.term;
val SIGKILL = Posix.Signal.kill;

fun kill_group pid s =
  let
    val arg = Posix.Process.K_GROUP (Posix.Process.wordToPid (LargeWord.fromInt pid));
    val _ = Posix.Process.kill (arg, s);
  in true end handle OS.SysErr _ => false;

end;
\<close>
