/*  Title:      Pure/Concurrent/bash.scala
    Author:     Makarius

GNU bash processes, with propagation of interrupts.
*/

package isabelle


import java.io.{File => JFile, BufferedReader, InputStreamReader,
  BufferedWriter, OutputStreamWriter}


object Bash
{
  /** result **/

  final case class Result(out_lines: List[String], err_lines: List[String], rc: Int)
  {
    def out: String = cat_lines(out_lines)
    def err: String = cat_lines(err_lines)
    def add_err(s: String): Result = copy(err_lines = err_lines ::: List(s))
    def set_rc(i: Int): Result = copy(rc = i)

    def check_error: Result =
      if (rc == Exn.Interrupt.return_code) throw Exn.Interrupt()
      else if (rc != 0) error(err)
      else this
  }



  /** process **/

  def process(cwd: JFile, env: Map[String, String], redirect: Boolean, args: String*): Process =
    new Process(cwd, env, redirect, args:_*)

  class Process private [Bash](
      cwd: JFile, env: Map[String, String], redirect: Boolean, args: String*)
    extends Prover.System_Process
  {
    private val params =
      List(File.standard_path(Path.explode("~~/lib/scripts/process")), "group", "-", "no_script")
    private val proc = Isabelle_System.execute_env(cwd, env, redirect, (params ::: args.toList):_*)


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

    private def cleanup() =
      try { Runtime.getRuntime.removeShutdownHook(shutdown_hook) }
      catch { case _: IllegalStateException => }


    /* result */

    def join: Int = { val rc = proc.waitFor; cleanup(); rc }
  }
}
