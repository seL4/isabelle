/*
 * Scala instance of Console plugin
 *
 * @author Makarius
 */

package isabelle.jedit


import console.{Console, ConsolePane, Shell, Output}

import org.gjt.sp.jedit.{jEdit, JARClassLoader}
import org.gjt.sp.jedit.MiscUtilities

import java.io.{File, Writer, PrintWriter}

import scala.tools.nsc.{Interpreter, GenericRunnerSettings, NewLinePrintWriter, ConsoleWriter}
import scala.collection.mutable


class Scala_Console extends Shell("Scala")
{
  /* global state -- owned by Swing thread */

  private var interpreters = Map[Console, Interpreter]()

  private var global_console: Console = null
  private var global_out: Output = null
  private var global_err: Output = null

  private def with_console[A](console: Console, out: Output, err: Output)(e: => A): A =
  {
    global_console = console
    global_out = out
    global_err = if (err == null) out else err
    val res = Exn.capture { e }
    global_console = null
    global_out = null
    global_err = null
    Exn.release(res)
  }

  private def report_error(str: String)
  {
    if (global_console == null || global_err == null) System.err.println(str)
    else global_err.print(global_console.getErrorColor, str)
  }

  private def construct_classpath(): String =
  {
    def find_jars(start: String): List[String] =
      if (start != null)
        Standard_System.find_files(new File(start),
          entry => entry.isFile && entry.getName.endsWith(".jar")).map(_.getAbsolutePath)
      else Nil
    val path =
      (jEdit.getJEditHome + File.separator + "jedit.jar") ::
        (find_jars(jEdit.getSettingsDirectory) ::: find_jars(jEdit.getJEditHome))
     path.mkString(File.pathSeparator)
  }

  private class Console_Writer extends Writer
  {
    def close {}
    def flush {}

    override def write(str: String)
    {
      if (global_out == null) System.out.println(str)
      else global_out.print(null, str)
    }

    def write(cbuf: Array[Char], off: Int, len: Int)
    {
      if (len > 0) write(new String(cbuf.subArray(off, off + len)))
    }
  }

  override def openConsole(console: Console)
  {
    val settings = new GenericRunnerSettings(report_error)
    settings.classpath.value = construct_classpath()
    val printer = new PrintWriter(new Console_Writer, true)

    val interp = new Interpreter(settings, printer)
    {
      override def parentClassLoader = new JARClassLoader
    }
    interp.setContextClassLoader
    interp.bind("view", "org.gjt.sp.jedit.View", console.getView)
    interp.bind("session", "isabelle.proofdocument.Session", Isabelle.session)
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
     "  view    -- current jEdit/Swing view (e.g. view.getBuffer, view.getTextArea)\n" +
     "  session -- Isabelle session (e.g. session.isabelle_system)\n")
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
