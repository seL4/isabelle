/*  Title:      Tools/jEdit/src/scala_console.scala
    Author:     Makarius

Scala instance of Console plugin.
*/

package isabelle.jedit


import isabelle._

import console.{Console, ConsolePane, Shell, Output}

import org.gjt.sp.jedit.{jEdit, JARClassLoader}
import org.gjt.sp.jedit.MiscUtilities

import java.lang.System
import java.io.{File => JFile, OutputStream, Writer, PrintWriter}

import scala.tools.nsc.{GenericRunnerSettings, NewLinePrintWriter, ConsoleWriter}
import scala.tools.nsc.interpreter.IMain
import scala.collection.mutable


class Scala_Console extends Shell("Scala")
{
  /* reconstructed jEdit/plugin classpath */

  private def reconstruct_classpath(): String =
  {
    def find_jars(start: String): List[String] =
      if (start != null)
        Standard_System.find_files(new JFile(start),
          entry => entry.isFile && entry.getName.endsWith(".jar")).map(_.getAbsolutePath)
      else Nil
    val path = find_jars(jEdit.getSettingsDirectory) ::: find_jars(jEdit.getJEditHome)
    path.mkString(JFile.pathSeparator)
  }


  /* global state -- owned by Swing thread */

  private var interpreters = Map[Console, IMain]()

  private var global_console: Console = null
  private var global_out: Output = null
  private var global_err: Output = null

  private val console_stream = new OutputStream
  {
    val buf = new StringBuilder
    override def flush()
    {
      val str = Standard_System.decode_permissive_utf8(buf.toString)
      buf.clear
      if (global_out == null) System.out.print(str)
      else Swing_Thread.now { global_out.writeAttrs(null, str) }
    }
    override def close() { flush () }
    def write(byte: Int) { buf.append(byte.toChar) }
  }

  private val console_writer = new Writer
  {
    def flush() {}
    def close() {}

    def write(cbuf: Array[Char], off: Int, len: Int)
    {
      if (len > 0) write(new String(cbuf.slice(off, off + len)))
    }

    override def write(str: String)
    {
      if (global_out == null) System.out.println(str)
      else global_out.print(null, str)
    }
  }

  private def with_console[A](console: Console, out: Output, err: Output)(e: => A): A =
  {
    global_console = console
    global_out = out
    global_err = if (err == null) out else err
    val res = Exn.capture { scala.Console.withOut(console_stream)(e) }
    console_stream.flush
    global_console = null
    global_out = null
    global_err = null
    Exn.release(res)
  }

  private def report_error(str: String)
  {
    if (global_console == null || global_err == null) System.err.println(str)
    else Swing_Thread.now { global_err.print(global_console.getErrorColor, str) }
  }


  /* jEdit console methods */

  override def openConsole(console: Console)
  {
    val settings = new GenericRunnerSettings(report_error)
    settings.classpath.value = reconstruct_classpath()

    val interp = new IMain(settings, new PrintWriter(console_writer, true))
    {
      override def parentClassLoader = new JARClassLoader
    }
    interp.setContextClassLoader
    interp.bind("view", "org.gjt.sp.jedit.View", console.getView)
    interp.bind("console", "console.Console", console)
    interp.interpret("import isabelle.jedit.Isabelle")

    interpreters += (console -> interp)
  }

  override def closeConsole(console: Console)
  {
    interpreters -= console
  }

  override def printInfoMessage(out: Output)
  {
    out.print(null,
     "This shell evaluates Isabelle/Scala expressions.\n\n" +
     "The following special toplevel bindings are provided:\n" +
     "  view      -- current jEdit/Swing view (e.g. view.getBuffer, view.getTextArea)\n" +
     "  console   -- jEdit Console plugin\n" +
     "  Isabelle  -- Isabelle plugin (e.g. Isabelle.session, Isabelle.document_model)\n")
  }

  override def printPrompt(console: Console, out: Output)
  {
    out.writeAttrs(ConsolePane.colorAttributes(console.getInfoColor), "scala>")
    out.writeAttrs(ConsolePane.colorAttributes(console.getPlainColor), " ")
  }

  override def execute(console: Console, input: String, out: Output, err: Output, command: String)
  {
    val interp = interpreters(console)
    with_console(console, out, err) { interp.interpret(command) }
    if (err != null) err.commandDone()
    out.commandDone()
  }

  override def stop(console: Console)
  {
    closeConsole(console)
    console.clear
    openConsole(console)
    val out = console.getOutput
    out.commandDone
    printPrompt(console, out)
  }
}
