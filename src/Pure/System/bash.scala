/*  Title:      Pure/System/bash.scala
    Author:     Makarius

GNU bash processes, with propagation of interrupts.
*/

package isabelle


import java.io.{File => JFile, BufferedReader, InputStreamReader,
  BufferedWriter, OutputStreamWriter}

import scala.annotation.tailrec


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

    private val script_file = Isabelle_System.tmp_file("bash_script")
    File.write(script_file, script)

    private val proc =
      Isabelle_System.process(
        List(File.platform_path(Path.variable("ISABELLE_BASH_PROCESS")), "-",
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

    private val pid = stdout.readLine

    @tailrec private def kill(signal: String, count: Int = 1): Boolean =
    {
      count <= 0 ||
      {
        Isabelle_System.kill(signal, pid)
        val running = Isabelle_System.kill("0", pid)._2 == 0
        if (running) {
          Time.seconds(0.1).sleep
          kill(signal, count - 1)
        }
        else false
      }
    }

    def terminate(): Unit = Isabelle_Thread.try_uninterruptible
    {
      kill("INT", count = 7) && kill("TERM", count = 3) && kill("KILL")
      proc.destroy
      do_cleanup()
    }

    def interrupt(): Unit = Isabelle_Thread.try_uninterruptible
    {
      Isabelle_System.kill("INT", pid)
    }


    // JVM shutdown hook

    private val shutdown_hook = Isabelle_Thread.create(() => terminate())

    try { Runtime.getRuntime.addShutdownHook(shutdown_hook) }
    catch { case _: IllegalStateException => }


    // cleanup

    private def do_cleanup()
    {
      try { Runtime.getRuntime.removeShutdownHook(shutdown_hook) }
      catch { case _: IllegalStateException => }

      script_file.delete

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
      stdin.close

      val out_lines =
        Future.thread("bash_stdout") { File.read_lines(stdout, progress_stdout) }
      val err_lines =
        Future.thread("bash_stderr") { File.read_lines(stderr, progress_stderr) }

      val watchdog_thread =
        for ((time, check) <- watchdog)
        yield {
          Future.thread("bash_watchdog") {
            while (proc.isAlive) {
              time.sleep
              if (check(this)) interrupt()
            }
          }
        }

      val rc =
        try { join }
        catch { case Exn.Interrupt() => terminate(); Exn.Interrupt.return_code }

      watchdog_thread.foreach(_.cancel)

      if (strict && rc == Exn.Interrupt.return_code) throw Exn.Interrupt()

      Process_Result(rc, out_lines.join, err_lines.join, get_timing)
    }
  }


  /* Scala function */

  object Process extends Scala.Fun("bash_process")
  {
    val here = Scala_Project.here
    def apply(script: String): String =
    {
      val result =
        Exn.capture {
          val proc = process(script)
          val res = proc.result()
          (res, proc.pid)
        }

      val is_interrupt =
        result match {
          case Exn.Res((res, _)) => res.rc == Exn.Interrupt.return_code
          case Exn.Exn(exn) => Exn.is_interrupt(exn)
        }

      val encode: XML.Encode.T[Exn.Result[(Process_Result, String)]] =
      {
        import XML.Encode._
        val string = XML.Encode.string
        variant(List(
          { case _ if is_interrupt => (Nil, Nil) },
          { case Exn.Exn(exn) => (Nil, string(Exn.message(exn))) },
          { case Exn.Res((res, pid)) =>
              val out = Library.terminate_lines(res.out_lines)
              val err = Library.terminate_lines(res.err_lines)
              (List(int_atom(res.rc), pid), pair(string, string)(out, err)) }))
      }
      YXML.string_of_body(encode(result))
    }
  }
}
