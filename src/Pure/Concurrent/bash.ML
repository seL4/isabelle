(*  Title:      Pure/Concurrent/bash.ML
    Author:     Makarius

GNU bash processes, with propagation of interrupts.
*)

local

fun read_file name =
  let val is = TextIO.openIn name
  in Exn.release (Exn.capture TextIO.inputAll is before TextIO.closeIn is) end;

fun write_file name txt =
  let val os = TextIO.openOut name
  in Exn.release (Exn.capture TextIO.output (os, txt) before TextIO.closeOut os) end;

in

fun bash_output script =
  Multithreading.with_attributes Multithreading.no_interrupts (fn orig_atts =>
    let
      val script_name = OS.FileSys.tmpName ();
      val _ = write_file script_name script;

      val pid_name = OS.FileSys.tmpName ();
      val output_name = OS.FileSys.tmpName ();

      (*result state*)
      datatype result = Wait | Signal | Result of int;
      val result = Unsynchronized.ref Wait;
      val lock = Mutex.mutex ();
      val cond = ConditionVar.conditionVar ();
      fun set_result res =
        (Mutex.lock lock; result := res; ConditionVar.signal cond; Mutex.unlock lock);

      val _ = Mutex.lock lock;

      (*system thread*)
      val system_thread = Thread.fork (fn () =>
        let
          val status =
            OS.Process.system ("exec \"$ISABELLE_HOME/lib/scripts/process\" group " ^ pid_name ^
              " script \"exec bash " ^ script_name ^ " > " ^ output_name ^ "\"");
          val res =
            (case Posix.Process.fromStatus status of
              Posix.Process.W_EXITED => Result 0
            | Posix.Process.W_EXITSTATUS 0wx82 => Signal
            | Posix.Process.W_EXITSTATUS w => Result (Word8.toInt w)
            | Posix.Process.W_SIGNALED s =>
                if s = Posix.Signal.int then Signal
                else Result (256 + LargeWord.toInt (Posix.Signal.toWord s))
            | Posix.Process.W_STOPPED s => Result (512 + LargeWord.toInt (Posix.Signal.toWord s)));
        in set_result res end handle _ (*sic*) => set_result (Result 2), []);

      (*main thread -- proxy for interrupts*)
      fun kill n =
        (case Int.fromString (read_file pid_name) of
          SOME pid =>
            Posix.Process.kill
              (Posix.Process.K_GROUP (Posix.Process.wordToPid (LargeWord.fromInt pid)),
                Posix.Signal.int)
        | NONE => ())
        handle OS.SysErr _ => () | IO.Io _ =>
          (OS.Process.sleep (seconds 0.1); if n > 0 then kill (n - 1) else ());

      val _ =
        while ! result = Wait do
          let val res =
            Multithreading.sync_wait (SOME orig_atts)
              (SOME (Time.+ (Time.now (), seconds 0.1))) cond lock
          in if Exn.is_interrupt_exn res then kill 10 else () end;

      (*cleanup*)
      val output = read_file output_name handle IO.Io _ => "";
      val _ = OS.FileSys.remove script_name handle OS.SysErr _ => ();
      val _ = OS.FileSys.remove pid_name handle OS.SysErr _ => ();
      val _ = OS.FileSys.remove output_name handle OS.SysErr _ => ();
      val _ = Thread.interrupt system_thread handle Thread _ => ();
      val rc = (case ! result of Signal => Exn.interrupt () | Result rc => rc);
    in (output, rc) end);

end;

