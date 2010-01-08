/*
 * Scala instance of Console plugin
 *
 * @author Makarius
 */

package isabelle.jedit


import console.{Console, ConsolePane, Shell, Output}

import org.gjt.sp.jedit.{jEdit, JARClassLoader}
import org.gjt.sp.jedit.MiscUtilities

import java.io.{Writer, PrintWriter}

import scala.tools.nsc.{Interpreter, GenericRunnerSettings, NewLinePrintWriter, ConsoleWriter}


class Scala_Console extends Shell("Scala")
{
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

  private class Console_Writer extends Writer
  {
    def close {}
    def flush {}

    def write(cbuf: Array[Char], off: Int, len: Int)
    {
      if (len > 0) write(new String(cbuf.subArray(off, off + len)))
    }

    override def write(str: String)
    {
      if (global_out == null) System.out.println(str)
      else global_out.print(null, str)
    }
  }

  override def openConsole(console: Console)
  {
    val settings = new GenericRunnerSettings(report_error)
    val printer = new PrintWriter(new Console_Writer, true)
    val interp = new Interpreter(settings, printer)
    {
      override def parentClassLoader = new JARClassLoader
    }
    interp.setContextClassLoader

    val view = console.getView
    val edit_pane = view.getEditPane
    interp.bind("view", "org.gjt.sp.jedit.View", view)
    interp.bind("editPane", "org.gjt.sp.jedit.EditPane", edit_pane)
    interp.bind("buffer", "org.gjt.sp.jedit.Buffer", edit_pane.getBuffer)
    interp.bind("textArea", "org.gjt.sp.jedit.textarea.JEditTextArea", edit_pane.getTextArea)
    interp.bind("wm", "org.gjt.sp.jedit.gui.DockableWindowManager", view.getDockableWindowManager)

    interpreters += (console -> interp)
  }

  override def closeConsole(console: Console)
  {
    interpreters -= console
  }

  override def printPrompt(console: Console, out: Output)
	{
    out.writeAttrs(ConsolePane.colorAttributes(console.getInfoColor), "scala>")
		out.writeAttrs(ConsolePane.colorAttributes(console.getPlainColor), " ")
	}

  override def execute(console: Console, input: String, out: Output, err: Output, command: String)
  {
    with_console(console, out, err) { interpreters(console).interpret(command) }
    if (err != null) err.commandDone()
		out.commandDone()
  }
}
