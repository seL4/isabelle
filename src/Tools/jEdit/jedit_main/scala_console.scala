/*  Title:      Tools/jEdit/jedit_main/scala_console.scala
    Author:     Makarius

Scala instance of Console plugin.
*/

package isabelle.jedit_main


import isabelle._
import isabelle.jedit._

import console.{Console, ConsolePane, Shell, Output}
import org.gjt.sp.jedit.JARClassLoader
import java.io.{OutputStream, Writer, PrintWriter}


object Scala_Console {
  class Interpreter(context: Scala.Compiler.Context, val console: Console)
    extends Scala.Interpreter(context)

  def console_interpreter(console: Console): Option[Interpreter] =
    Scala.Interpreter.get { case int: Interpreter if int.console == console => int }

  def running_interpreter(): Interpreter = {
    val self = Thread.currentThread()
    Scala.Interpreter.get { case int: Interpreter if int.running_thread(self) => int }
      .getOrElse(error("Bad Scala interpreter thread"))
  }

  def running_console(): Console = running_interpreter().console

  val init = """
import isabelle._
import isabelle.jedit._
val console = isabelle.jedit_main.Scala_Console.running_console()
val view = console.getView()
"""
}

class Scala_Console extends Shell("Scala") {
  /* global state -- owned by GUI thread */

  @volatile private var global_console: Console = null
  @volatile private var global_out: Output = null
  @volatile private var global_err: Output = null

  private val console_stream = new OutputStream {
    val buf = new StringBuilder(100)

    override def flush(): Unit = {
      val s = buf.synchronized { val s = buf.toString; buf.clear(); s }
      val str = UTF8.decode_permissive(s)
      GUI_Thread.later {
        if (global_out == null) java.lang.System.out.print(str)
        else global_out.writeAttrs(null, str)
      }
      Time.seconds(0.01).sleep()  // FIXME adhoc delay to avoid loosing output
    }

    override def close(): Unit = flush()

    def write(byte: Int): Unit = {
      val c = byte.toChar
      buf.synchronized { buf.append(c) }
      if (c == '\n') flush()
    }
  }

  private val console_writer = new Writer {
    def flush(): Unit = console_stream.flush()
    def close(): Unit = console_stream.flush()

    def write(cbuf: Array[Char], off: Int, len: Int): Unit = {
      if (len > 0) {
        UTF8.bytes(new String(cbuf.slice(off, off + len))).foreach(console_stream.write(_))
      }
    }
  }

  private def with_console[A](console: Console, out: Output, err: Output)(e: => A): A = {
    global_console = console
    global_out = out
    global_err = if (err == null) out else err
    try {
      scala.Console.withErr(console_stream) {
        scala.Console.withOut(console_stream) { e }
      }
    }
    finally {
      console_stream.flush()
      global_console = null
      global_out = null
      global_err = null
    }
  }

  private def report_error(str: String): Unit = {
    if (global_console == null || global_err == null) isabelle.Output.writeln(str)
    else GUI_Thread.later { global_err.print(global_console.getErrorColor, str) }
  }


  /* jEdit console methods */

  override def openConsole(console: Console): Unit = {
    val context =
      Scala.Compiler.context(
      print_writer = new PrintWriter(console_writer, true),
      error = report_error,
      jar_dirs = JEdit_Lib.directories,
      class_loader = Some(new JARClassLoader))

    val interpreter = new Scala_Console.Interpreter(context, console)
    interpreter.execute(_.interp.interpret(Scala_Console.init))
  }

  override def closeConsole(console: Console): Unit =
    Scala_Console.console_interpreter(console).foreach(_.shutdown())

  override def printInfoMessage(out: Output): Unit = {
    out.print(null,
     "This shell evaluates Isabelle/Scala expressions.\n\n" +
     "The contents of package isabelle and isabelle.jedit are imported.\n" +
     "The following special toplevel bindings are provided:\n" +
     "  view    -- current jEdit/Swing view (e.g. view.getBuffer, view.getTextArea)\n" +
     "  console -- jEdit Console plugin\n" +
     "  PIDE    -- Isabelle/PIDE plugin (e.g. PIDE.session, PIDE.snapshot, PIDE.rendering)\n")
  }

  override def printPrompt(console: Console, out: Output): Unit = {
    out.writeAttrs(ConsolePane.colorAttributes(console.getInfoColor), "scala>")
    out.writeAttrs(ConsolePane.colorAttributes(console.getPlainColor), " ")
  }

  override def execute(
    console: Console,
    input: String,
    out: Output,
    err: Output,
    command: String
  ): Unit = {
    Scala_Console.console_interpreter(console).foreach(interpreter =>
      interpreter.execute { context =>
        with_console(console, out, err) { context.interp.interpret(command) }
        GUI_Thread.later {
          Option(err).foreach(_.commandDone())
          out.commandDone()
        }
      })
  }

  override def stop(console: Console): Unit =
    Scala_Console.console_interpreter(console).foreach(_.shutdown())
}
