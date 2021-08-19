/*  Title:      Pure/System/bash.scala
    Author:     Makarius

Support for GNU bash: portable external processes with propagation of
interrupts.
*/

package isabelle


import java.util.{LinkedList, List => JList, Map => JMap}
import java.io.{BufferedReader, BufferedWriter, InputStreamReader, OutputStreamWriter, File => JFile}
import scala.annotation.tailrec
import scala.jdk.OptionConverters._


object Bash
{
  /* concrete syntax */

  private def bash_chr(c: Byte): String =
  {
    val ch = c.toChar
    ch match {
      case '\t' => "$'\\t'"
      case '\n' => "$'\\n'"
      case '\f' => "$'\\f'"
      case '\r' => "$'\\r'"
      case _ =>
        if (Symbol.is_ascii_letter(ch) || Symbol.is_ascii_digit(ch) || "+,-./:_".contains(ch))
          Symbol.ascii(ch)
        else if (c < 0) "$'\\x" + Integer.toHexString(256 + c) + "'"
        else if (c < 16) "$'\\x0" + Integer.toHexString(c) + "'"
        else if (c < 32 || c >= 127) "$'\\x" + Integer.toHexString(c) + "'"
        else  "\\" + ch
    }
  }

  def string(s: String): String =
    if (s == "") "\"\""
    else UTF8.bytes(s).iterator.map(bash_chr).mkString

  def strings(ss: List[String]): String =
    ss.iterator.map(Bash.string).mkString(" ")


  /* process and result */

  type Watchdog = (Time, Process => Boolean)

  def process(script: String,
      cwd: JFile = null,
      env: JMap[String, String] = Isabelle_System.settings(),
      redirect: Boolean = false,
      cleanup: () => Unit = () => ()): Process =
    new Process(script, cwd, env, redirect, cleanup)

  class Process private[Bash](
      script: String,
      cwd: JFile,
      env: JMap[String, String],
      redirect: Boolean,
      cleanup: () => Unit)
  {
    private val timing_file = Isabelle_System.tmp_file("bash_timing")
    private val timing = Synchronized[Option[Timing]](None)
    def get_timing: Timing = timing.value getOrElse Timing.zero

    private val winpid_file: Option[JFile] =
      if (Platform.is_windows) Some(Isabelle_System.tmp_file("bash_winpid")) else None
    private val winpid_script =
      winpid_file match {
        case None => script
        case Some(file) =>
          "read < /proc/self/winpid > /dev/null 2> /dev/null\n" +
          """echo -n "$REPLY" > """ + File.bash_path(file) + "\n\n" + script
      }

    private val script_file: JFile = Isabelle_System.tmp_file("bash_script")
    File.write(script_file, winpid_script)

    private val proc =
      isabelle.setup.Environment.process_builder(
        JList.of(File.platform_path(Path.variable("ISABELLE_BASH_PROCESS")),
          File.standard_path(timing_file), "bash", File.standard_path(script_file)),
        cwd, env, redirect).start()


    // channels

    val stdin: BufferedWriter =
      new BufferedWriter(new OutputStreamWriter(proc.getOutputStream, UTF8.charset))

    val stdout: BufferedReader =
      new BufferedReader(new InputStreamReader(proc.getInputStream, UTF8.charset))

    val stderr: BufferedReader =
      new BufferedReader(new InputStreamReader(proc.getErrorStream, UTF8.charset))


    // signals

    private val group_pid = stdout.readLine

    private def process_alive(pid: String): Boolean =
      (for {
        p <- Value.Long.unapply(pid)
        handle <- ProcessHandle.of(p).toScala
      } yield handle.isAlive) getOrElse false

    private def root_process_alive(): Boolean =
      winpid_file match {
        case None => process_alive(group_pid)
        case Some(file) =>
          file.exists() && process_alive(Library.trim_line(File.read(file)))
      }

    @tailrec private def signal(s: String, count: Int = 1): Boolean =
    {
      count <= 0 ||
      {
        isabelle.setup.Environment.kill_process(group_pid, s)
        val running =
          root_process_alive() ||
          isabelle.setup.Environment.kill_process(group_pid, "0")
        if (running) {
          Time.seconds(0.1).sleep()
          signal(s, count - 1)
        }
        else false
      }
    }

    def terminate(): Unit = Isabelle_Thread.try_uninterruptible
    {
      signal("INT", count = 7) && signal("TERM", count = 3) && signal("KILL")
      proc.destroy()
      do_cleanup()
    }

    def interrupt(): Unit = Isabelle_Thread.try_uninterruptible
    {
      isabelle.setup.Environment.kill_process(group_pid, "INT")
    }


    // JVM shutdown hook

    private val shutdown_hook = Isabelle_Thread.create(() => terminate())

    try { Runtime.getRuntime.addShutdownHook(shutdown_hook) }
    catch { case _: IllegalStateException => }


    // cleanup

    private def do_cleanup(): Unit =
    {
      try { Runtime.getRuntime.removeShutdownHook(shutdown_hook) }
      catch { case _: IllegalStateException => }

      script_file.delete()
      winpid_file.foreach(_.delete())

      timing.change {
        case None =>
          if (timing_file.isFile) {
            val t =
              Word.explode(File.read(timing_file)) match {
                case List(Value.Long(elapsed), Value.Long(cpu)) =>
                  Timing(Time.ms(elapsed), Time.ms(cpu), Time.zero)
                case _ => Timing.zero
              }
            timing_file.delete
            Some(t)
          }
          else Some(Timing.zero)
        case some => some
      }

      cleanup()
    }


    // join

    def join(): Int =
    {
      val rc = proc.waitFor()
      do_cleanup()
      rc
    }


    // result

    def result(
      input: String = "",
      progress_stdout: String => Unit = (_: String) => (),
      progress_stderr: String => Unit = (_: String) => (),
      watchdog: Option[Watchdog] = None,
      strict: Boolean = true): Process_Result =
    {
      val in =
        if (input.isEmpty) Future.value(stdin.close())
        else Future.thread("bash_stdin") { stdin.write(input); stdin.flush(); stdin.close(); }
      val out_lines =
        Future.thread("bash_stdout") { File.read_lines(stdout, progress_stdout) }
      val err_lines =
        Future.thread("bash_stderr") { File.read_lines(stderr, progress_stderr) }

      val watchdog_thread =
        for ((time, check) <- watchdog)
        yield {
          Future.thread("bash_watchdog") {
            while (proc.isAlive) {
              time.sleep()
              if (check(this)) interrupt()
            }
          }
        }

      val rc =
        try { join() }
        catch { case Exn.Interrupt() => terminate(); Process_Result.interrupt_rc }

      watchdog_thread.foreach(_.cancel())

      in.join
      out_lines.join
      err_lines.join

      if (strict && rc == Process_Result.interrupt_rc) throw Exn.Interrupt()

      Process_Result(rc, out_lines.join, err_lines.join, get_timing)
    }
  }


  /* server */

  object Server
  {
    // input messages
    private val RUN = "run"
    private val KILL = "kill"

    // output messages
    private val UUID = "uuid"
    private val INTERRUPT = "interrupt"
    private val FAILURE = "failure"
    private val RESULT = "result"

    def start(port: Int = 0, debugging: => Boolean = false): Server =
    {
      val server = new Server(port, debugging)
      server.start()
      server
    }
  }

  class Server private(port: Int, debugging: => Boolean)
    extends isabelle.Server.Handler(port)
  {
    server =>

    private val _processes = Synchronized(Map.empty[UUID.T, Bash.Process])

    override def stop(): Unit =
    {
      for ((_, process) <- _processes.value) process.terminate()
      super.stop()
    }

    override def handle(connection: isabelle.Server.Connection): Unit =
    {
      def reply(chunks: List[String]): Unit =
        connection.write_byte_message(chunks.map(Bytes.apply))

      def reply_failure(exn: Throwable): Unit =
        reply(
          if (Exn.is_interrupt(exn)) List(Server.INTERRUPT)
          else List(Server.FAILURE, Exn.message(exn)))

      def reply_result(result: Process_Result): Unit =
        reply(
          Server.RESULT ::
          result.rc.toString ::
          result.timing.elapsed.ms.toString ::
          result.timing.cpu.ms.toString ::
          result.out_lines.length.toString ::
          result.out_lines :::
          result.err_lines)

      connection.read_byte_message().map(_.map(_.text)) match {
        case None =>

        case Some(List(Server.KILL, UUID(uuid))) =>
          if (debugging) Output.writeln("kill " + uuid)
          _processes.value.get(uuid).foreach(_.terminate())

        case Some(List(Server.RUN, script, input, cwd, putenv,
            Value.Boolean(redirect), Value.Seconds(timeout), description)) =>
          val uuid = UUID.random()

          val descr = proper_string(description) getOrElse "bash_process"
          if (debugging) {
            Output.writeln(
              "start " + quote(descr) + " (uuid=" + uuid + ", timeout=" + timeout.seconds + ")")
          }

          Exn.capture {
            Bash.process(script,
              cwd =
                XML.Decode.option(XML.Decode.string)(YXML.parse_body(cwd)) match {
                  case None => null
                  case Some(s) => Path.explode(s).file
                },
              env =
                Isabelle_System.settings(
                  XML.Decode.list(XML.Decode.pair(XML.Decode.string, XML.Decode.string))(
                    YXML.parse_body(putenv))),
              redirect= redirect)
          }
          match {
            case Exn.Exn(exn) => reply_failure(exn)
            case Exn.Res(process) =>
              _processes.change(processes => processes + (uuid -> process))
              reply(List(Server.UUID, uuid.toString))

              Isabelle_Thread.fork(name = "bash_process") {
                @volatile var is_timeout = false
                val watchdog: Option[Watchdog] =
                  if (timeout.is_zero) None else Some((timeout, _ => { is_timeout = true; true }))

                Exn.capture { process.result(input = input, watchdog = watchdog, strict = false) }
                match {
                  case Exn.Exn(exn) => reply_failure(exn)
                  case Exn.Res(res0) =>
                    val res = if (!res0.ok && is_timeout) res0.timeout_rc else res0
                    if (debugging) {
                      Output.writeln(
                        "stop " + quote(descr) + " (uuid=" + uuid + ", return_code=" + res.rc + ")")
                    }
                    reply_result(res)
                }

                _processes.change(provers => provers - uuid)
              }

              connection.await_close()
          }

        case Some(_) => reply_failure(ERROR("Bad protocol message"))
      }
    }
  }

  class Handler extends Session.Protocol_Handler
  {
    private var server: Server = null

    override def init(session: Session): Unit =
    {
      exit()
      server = Server.start(debugging = session.session_options.bool("bash_process_debugging"))
    }

    override def exit(): Unit =
    {
      if (server != null) {
        server.stop()
        server = null
      }
    }

    override def prover_options(options: Options): Options =
    {
      val address = if (server == null) "" else server.address
      val password = if (server == null) "" else server.password
      options +
        ("bash_process_address=" + address) +
        ("bash_process_password=" + password)
    }
  }
}
