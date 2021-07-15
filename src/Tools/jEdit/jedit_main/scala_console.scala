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


class Scala_Console extends Shell("Scala")
{
  /* global state -- owned by GUI thread */

  @volatile private var interpreters = Map.empty[Console, Interpreter]

  @volatile private var global_console: Console = null
  @volatile private var global_out: Output = null
  @volatile private var global_err: Output = null

  private val console_stream = new OutputStream
  {
    val buf = new StringBuilder(100)

    override def flush(): Unit =
    {
      val s = buf.synchronized { val s = buf.toString; buf.clear(); s }
      val str = UTF8.decode_permissive(s)
      GUI_Thread.later {
        if (global_out == null) System.out.print(str)
        else global_out.writeAttrs(null, str)
      }
      Time.seconds(0.01).sleep()  // FIXME adhoc delay to avoid loosing output
    }

    override def close(): Unit = flush()

    def write(byte: Int): Unit =
    {
      val c = byte.toChar
      buf.synchronized { buf.append(c) }
      if (c == '\n') flush()
    }
  }

  private val console_writer = new Writer
  {
    def flush(): Unit = console_stream.flush()
    def close(): Unit = console_stream.flush()

    def write(cbuf: Array[Char], off: Int, len: Int): Unit =
    {
      if (len > 0) {
        UTF8.bytes(new String(cbuf.slice(off, off + len))).foreach(console_stream.write(_))
      }
    }
  }

  private def with_console[A](console: Console, out: Output, err: Output)(e: => A): A =
  {
    global_console = console
    global_out = out
    global_err = if (err == null) out else err
    try {
      scala.Console.withErr(console_stream) {
        scala.Console.withOut(console_stream) { e }
      }
    }
    finally {
      console_stream.flush
      global_console = null
      global_out = null
      global_err = null
    }
  }

  private def report_error(str: String): Unit =
  {
    if (global_console == null || global_err == null) isabelle.Output.writeln(str)
    else GUI_Thread.later { global_err.print(global_console.getErrorColor, str) }
  }


  /* interpreter thread */

  private abstract class Request
  private case class Start(console: Console) extends Request
  private case class Execute(console: Console, out: Output, err: Output, command: String)
    extends Request

  private class Interpreter
  {
    private val running = Synchronized[Option[Thread]](None)
    def interrupt(): Unit = running.change(opt => { opt.foreach(_.interrupt()); opt })

    private val interp =
      Scala.Compiler.context(error = report_error, jar_dirs = JEdit_Lib.directories).
        interpreter(
          print_writer = new PrintWriter(console_writer, true),
          class_loader = new JARClassLoader)

    val thread: Consumer_Thread[Request] = Consumer_Thread.fork("Scala_Console")
    {
      case Start(console) =>
        interp.bind("view", "org.gjt.sp.jedit.View", console.getView)
        interp.bind("console", "console.Console", console)
        interp.interpret("import isabelle._; import isabelle.jedit._")
        true

      case Execute(console, out, err, command) =>
        with_console(console, out, err) {
          try {
            running.change(_ => Some(Thread.currentThread()))
            interp.interpret(command)
          }
          finally {
            running.change(_ => None)
            Exn.Interrupt.dispose()
          }
          GUI_Thread.later {
            if (err != null) err.commandDone()
            out.commandDone()
          }
          true
        }
    }
  }


  /* jEdit console methods */

  override def openConsole(console: Console): Unit =
  {
    val interp = new Interpreter
    interp.thread.send(Start(console))
    interpreters += (console -> interp)
  }

  override def closeConsole(console: Console): Unit =
  {
    interpreters.get(console) match {
      case Some(interp) =>
        interp.interrupt()
        interp.thread.shutdown()
        interpreters -= console
      case None =>
    }
  }

  override def printInfoMessage(out: Output): Unit =
  {
    out.print(null,
     "This shell evaluates Isabelle/Scala expressions.\n\n" +
     "The contents of package isabelle and isabelle.jedit are imported.\n" +
     "The following special toplevel bindings are provided:\n" +
     "  view    -- current jEdit/Swing view (e.g. view.getBuffer, view.getTextArea)\n" +
     "  console -- jEdit Console plugin\n" +
     "  PIDE    -- Isabelle/PIDE plugin (e.g. PIDE.session, PIDE.snapshot, PIDE.rendering)\n")
  }

  override def printPrompt(console: Console, out: Output): Unit =
  {
    out.writeAttrs(ConsolePane.colorAttributes(console.getInfoColor), "scala>")
    out.writeAttrs(ConsolePane.colorAttributes(console.getPlainColor), " ")
  }

  override def execute(
    console: Console, input: String, out: Output, err: Output, command: String): Unit =
  {
    interpreters(console).thread.send(Execute(console, out, err, command))
  }

  override def stop(console: Console): Unit =
    interpreters.get(console).foreach(_.interrupt())
}
