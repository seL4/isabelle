(*  Title:      Pure/General/system_process.ML
    ID:         $Id$
    Author:     Makarius

System shell processes, with static input/output and propagation of interrupts.
*)

signature SYSTEM_PROCESS =
sig
  val system_out: string -> string * int
  val system: string -> int
end;

structure SystemProcess: SYSTEM_PROCESS =
struct

fun system_out script = uninterruptible (fn restore_attributes => fn () =>
  let
    val _ = Secure.deny_secure "Cannot execute shell commands in secure mode";

    val script_file = OS.FileSys.tmpName ();
    val _ = File.write (Path.explode script_file) script;

    val perl_file = OS.FileSys.tmpName ();
    val _ = File.write (Path.explode perl_file)  (*robust signal handling via perl*)
      ("$SIG{'INT'} = 'DEFAULT'; exec '/bin/bash --norc " ^ script_file ^ "' || die $!;");

    val proc = Unix.execute ("/usr/bin/env", ["perl", "-w", perl_file]);
    val (proc_stdout, proc_stdin) = Unix.streamsOf proc;

    fun read buf =
      (case Exn.capture (restore_attributes TextIO.input) proc_stdout of
        Exn.Exn Interrupt => (Unix.kill (proc, Posix.Signal.int); read buf)
      | Exn.Exn _ => buf
      | Exn.Result "" => buf
      | Exn.Result txt => read (Buffer.add txt buf));

    val output = read Buffer.empty;
    val status = Unix.reap proc;
    val rc = Unix.fromStatus status;

    val _ = OS.FileSys.remove script_file;
    val _ = OS.FileSys.remove perl_file;
  in
    if rc = Unix.W_SIGNALED Posix.Signal.int orelse rc = Unix.W_EXITSTATUS 0wx82
    then raise Interrupt
    else (Buffer.content output, if OS.Process.isSuccess status then 0 else 1)
  end) ();

fun system script =
  let val (output, status) = system_out script in writeln output; status end;

end;

