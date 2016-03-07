/*  Title:      Pure/Concurrent/bash.scala
    Author:     Makarius

GNU bash processes, with propagation of interrupts.
*/

package isabelle


import java.io.{File => JFile, BufferedReader, InputStreamReader,
  BufferedWriter, OutputStreamWriter}


object Bash
{
  private class Limited_Progress(proc: Process, progress_limit: Option[Long])
  {
    private var count = 0L
    def apply(progress: String => Unit)(line: String): Unit = synchronized {
      progress(line)
      count = count + line.length + 1
      progress_limit match {
        case Some(limit) if count > limit => proc.terminate
        case _ =>
      }
    }
  }

  def process(script: String,
      cwd: JFile = null, env: Map[String, String] = null, redirect: Boolean = false): Process =
    new Process(script, cwd, env, redirect)

  class Process private [Bash](
      script: String, cwd: JFile, env: Map[String, String], redirect: Boolean)
    extends Prover.System_Process
  {
    val script_file = Isabelle_System.tmp_file("bash_script")
    File.write(script_file, script)

    private val proc =
      Isabelle_System.process(cwd, Isabelle_System.settings(env), redirect,
        File.platform_path(Path.variable("ISABELLE_BASH_PROCESS")), "-",
          "bash", File.standard_path(script_file))


    // channels

    val stdin: BufferedWriter =
      new BufferedWriter(new OutputStreamWriter(proc.getOutputStream, UTF8.charset))

    val stdout: BufferedReader =
      new BufferedReader(new InputStreamReader(proc.getInputStream, UTF8.charset))

    val stderr: BufferedReader =
      new BufferedReader(new InputStreamReader(proc.getErrorStream, UTF8.charset))


    // signals

    private val pid = stdout.readLine

    private def kill(signal: String): Boolean =
      Exn.Interrupt.postpone {
        Isabelle_System.kill(signal, pid)
        Isabelle_System.kill("0", pid)._2 == 0 } getOrElse true

    private def multi_kill(signal: String): Boolean =
    {
      var running = true
      var count = 10
      while (running && count > 0) {
        if (kill(signal)) {
          Exn.Interrupt.postpone {
            Thread.sleep(100)
            count -= 1
          }
        }
        else running = false
      }
      running
    }

    def interrupt() { multi_kill("INT") }
    def terminate() { multi_kill("INT") && multi_kill("TERM") && kill("KILL"); proc.destroy }


    // JVM shutdown hook

    private val shutdown_hook = new Thread { override def run = terminate() }

    try { Runtime.getRuntime.addShutdownHook(shutdown_hook) }
    catch { case _: IllegalStateException => }


    /* join */

    def join: Int =
    {
      val rc = proc.waitFor

      try { Runtime.getRuntime.removeShutdownHook(shutdown_hook) }
      catch { case _: IllegalStateException => }

      script_file.delete

      rc
    }


    /* result */

    def result(
      progress_stdout: String => Unit = (_: String) => (),
      progress_stderr: String => Unit = (_: String) => (),
      progress_limit: Option[Long] = None,
      strict: Boolean = true): Process_Result =
    {
      stdin.close

      val limited = new Limited_Progress(this, progress_limit)
      val out_lines =
        Future.thread("bash_stdout") { File.read_lines(stdout, limited(progress_stdout)) }
      val err_lines =
        Future.thread("bash_stderr") { File.read_lines(stderr, limited(progress_stderr)) }

      val rc =
        try { join }
        catch { case Exn.Interrupt() => terminate; Exn.Interrupt.return_code }
      if (strict && rc == Exn.Interrupt.return_code) throw Exn.Interrupt()

      Process_Result(rc, out_lines.join, err_lines.join)
    }
  }
}
