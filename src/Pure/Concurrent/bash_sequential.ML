(*  Title:      Pure/Concurrent/bash_sequential.ML
    Author:     Makarius

Generic GNU bash processes (no provisions to propagate interrupts, but
could work via the controlling tty).
*)

signature BASH =
sig
  val process: string -> {output: string, rc: int, terminate: unit -> unit}
end;

structure Bash: BASH =
struct

fun process script =
  let
    val id = serial_string ();
    val script_path = File.tmp_path (Path.basic ("bash_script" ^ id));
    val output_path = File.tmp_path (Path.basic ("bash_output" ^ id));
    fun cleanup () = (try File.rm script_path; try File.rm output_path);
  in
    let
      val _ = File.write script_path script;
      val status =
        OS.Process.system
          ("exec \"$ISABELLE_HOME/lib/scripts/process\" no_group /dev/null" ^
            " script \"exec bash " ^ File.shell_path script_path ^ " > " ^
            File.shell_path output_path ^ "\"");
      val rc =
        (case Posix.Process.fromStatus status of
          Posix.Process.W_EXITED => 0
        | Posix.Process.W_EXITSTATUS w => Word8.toInt w
        | Posix.Process.W_SIGNALED s => 256 + LargeWord.toInt (Posix.Signal.toWord s)
        | Posix.Process.W_STOPPED s => 512 + LargeWord.toInt (Posix.Signal.toWord s));

      val output = the_default "" (try File.read output_path);
      val _ = cleanup ();
    in {output = output, rc = rc, terminate = fn () => ()} end
    handle exn => (cleanup (); reraise exn)
  end;

end;

