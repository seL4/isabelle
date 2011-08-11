(*  Title:      Pure/Concurrent/bash.ML
    Author:     Makarius

GNU bash processes, with propagation of interrupts.
*)

signature BASH =
sig
  val process: string -> {output: string, rc: int, terminate: unit -> unit}
end;

structure Bash: BASH =
struct

val process = uninterruptible (fn restore_attributes => fn script =>
  let
    datatype result = Wait | Signal | Result of int;
    val result = Synchronized.var "bash_result" Wait;

    val id = serial_string ();
    val script_path = File.tmp_path (Path.basic ("bash_script" ^ id));
    val output_path = File.tmp_path (Path.basic ("bash_output" ^ id));
    val pid_path = File.tmp_path (Path.basic ("bash_pid" ^ id));

    val system_thread =
      Simple_Thread.fork false (fn () =>
        Multithreading.with_attributes Multithreading.private_interrupts (fn _ =>
          let
            val _ = File.write script_path script;
            val status =
              OS.Process.system
                ("exec \"$ISABELLE_HOME/lib/scripts/process\" group " ^
                  File.shell_path pid_path ^ " script \"exec bash " ^
                  File.shell_path script_path ^ " > " ^
                  File.shell_path output_path ^ "\"");
            val res =
              (case Posix.Process.fromStatus status of
                Posix.Process.W_EXITED => Result 0
              | Posix.Process.W_EXITSTATUS 0wx82 => Signal
              | Posix.Process.W_EXITSTATUS w => Result (Word8.toInt w)
              | Posix.Process.W_SIGNALED s =>
                  if s = Posix.Signal.int then Signal
                  else Result (256 + LargeWord.toInt (Posix.Signal.toWord s))
              | Posix.Process.W_STOPPED s =>
                  Result (512 + LargeWord.toInt (Posix.Signal.toWord s)));
          in Synchronized.change result (K res) end
          handle exn =>
            (Synchronized.change result (fn Wait => Signal | res => res); reraise exn)));

    fun get_pid () = Int.fromString (File.read pid_path) handle IO.Io _ => NONE;

    fun terminate opt_pid =
      let
        val sig_test = Posix.Signal.fromWord 0w0;

        fun kill_group pid s =
          (Posix.Process.kill
            (Posix.Process.K_GROUP (Posix.Process.wordToPid (LargeWord.fromInt pid)), s); true)
          handle OS.SysErr _ => false;

        fun kill s =
          (case opt_pid of
            NONE => true
          | SOME pid => (kill_group pid s; kill_group pid sig_test));

        fun multi_kill count s =
          count = 0 orelse
            kill s andalso (OS.Process.sleep (seconds 0.1); multi_kill (count - 1) s);
        val _ =
          multi_kill 10 Posix.Signal.int andalso
          multi_kill 10 Posix.Signal.term andalso
          multi_kill 10 Posix.Signal.kill;
      in () end;

    fun cleanup () =
     (Simple_Thread.interrupt_unsynchronized system_thread;
      try File.rm script_path;
      try File.rm output_path;
      try File.rm pid_path);
  in
    let
      val _ =
        restore_attributes (fn () =>
          Synchronized.guarded_access result (fn Wait => NONE | x => SOME ((), x))) ();

      val output = the_default "" (try File.read output_path);
      val rc = (case Synchronized.value result of Signal => Exn.interrupt () | Result rc => rc);
      val pid = get_pid ();
      val _ = cleanup ();
    in {output = output, rc = rc, terminate = fn () => terminate pid} end
    handle exn => (terminate (get_pid ()); cleanup (); reraise exn)
  end);

end;

