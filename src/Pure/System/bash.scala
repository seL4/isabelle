/*  Title:      Pure/System/bash.scala
    Author:     Makarius

GNU bash processes, with propagation of interrupts.
*/

package isabelle


import java.util.{LinkedList, List => JList}
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

  def process_signal(group_pid: String, signal: String = "0"): Boolean =
  {
    val cmd = new LinkedList[String]
    if (Platform.is_windows) {
      cmd.add(Isabelle_System.cygwin_root() + "\\bin\\bash.exe")
    }
    else {
      cmd.add("/usr/bin/env")
      cmd.add("bash")
    }
    cmd.add("-c")
    cmd.add("kill -" + signal + " -" + group_pid)
    val (_, rc) = Isabelle_Env.process_output(Isabelle_Env.process(cmd))
    rc == 0
  }

  def process(script: String,
      cwd: JFile = null,
      env: Map[String, String] = Isabelle_System.settings(),
      redirect: Boolean = false,
      cleanup: () => Unit = () => ()): Process =
    new Process(script, cwd, env, redirect, cleanup)

  class Process private[Bash](
      script: String,
      cwd: JFile,
      env: Map[String, String],
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
      Isabelle_Env.process(
        JList.of(File.platform_path(Path.variable("ISABELLE_BASH_PROCESS")),
          File.standard_path(timing_file), "bash", File.standard_path(script_file)),
        cwd = cwd, env = env, redirect = redirect)


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
        process_signal(group_pid, signal = s)
        val running = root_process_alive() || process_signal(group_pid)
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
      process_signal(group_pid, "INT")
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

    def join: Int =
    {
      val rc = proc.waitFor
      do_cleanup()
      rc
    }


    // result

    def result(
      progress_stdout: String => Unit = (_: String) => (),
      progress_stderr: String => Unit = (_: String) => (),
      watchdog: Option[Watchdog] = None,
      strict: Boolean = true): Process_Result =
    {
      stdin.close()

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
        try { join }
        catch { case Exn.Interrupt() => terminate(); Exn.Interrupt.return_code }

      watchdog_thread.foreach(_.cancel())

      if (strict && rc == Exn.Interrupt.return_code) throw Exn.Interrupt()

      Process_Result(rc, out_lines.join, err_lines.join, get_timing)
    }
  }


  /* Scala function */

  object Process extends Scala.Fun_Strings("bash_process", thread = true)
  {
    val here = Scala_Project.here
    def apply(args: List[String]): List[String] =
    {
      val result =
        Exn.capture {
          val redirect = args.head == "true"
          val script = cat_lines(args.tail)
          Isabelle_System.bash(script, redirect = redirect)
        }

      val is_interrupt =
        result match {
          case Exn.Res(res) => res.rc == Exn.Interrupt.return_code
          case Exn.Exn(exn) => Exn.is_interrupt(exn)
        }

      result match {
        case _ if is_interrupt => Nil
        case Exn.Exn(exn) => List(Exn.message(exn))
        case Exn.Res(res) =>
          res.rc.toString ::
          res.timing.elapsed.ms.toString ::
          res.timing.cpu.ms.toString ::
          res.out_lines.length.toString ::
          res.out_lines ::: res.err_lines
      }
    }
  }
}
