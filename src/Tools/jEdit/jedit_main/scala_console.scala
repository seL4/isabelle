/*  Title:      Tools/jEdit/jedit_main/scala_console.scala
    Author:     Makarius

Scala instance of Console plugin.
*/

package isabelle.jedit_main


import isabelle._
import isabelle.jedit._

import console.{Console, ConsolePane, Shell, Output}
import org.gjt.sp.jedit.JARClassLoader

import java.io.OutputStream
import java.util.Objects
import javax.swing.text.{SimpleAttributeSet, StyleConstants}


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

  class Progress(
    val console: Console = running_console(),
    verbose: Boolean = false,
    threshold: Time = Build.progress_threshold(Options.defaults),
    detailed: Boolean = false,
    stderr: Boolean = false
  ) extends Console_Progress(
    verbose = verbose,
    threshold = threshold,
    detailed = detailed,
    stderr = stderr
  ) with isabelle.Progress.Local_Interrupts {
    override def status_hide(msgs: isabelle.Progress.Output): Unit = {
      val txt = output_text(msgs.map(isabelle.Progress.output_theory), terminate = true)
      val m = txt.length
      if (m > 0) {
        GUI_Thread.later {
          val doc = console.getConsolePane.getStyledDocument
          doc.remove(doc.getLength - m, m)
        }
      }
    }

    override def status_output(msgs: isabelle.Progress.Output): Unit = {
      if (msgs.nonEmpty) {
        GUI_Thread.later {
          for (msg <- msgs if do_output(msg)) {
            val attrs =
              if (msg.status) {
                val attrs = new SimpleAttributeSet
                StyleConstants.setBackground(attrs, console.getPlainColor)
                StyleConstants.setForeground(attrs, console.getBackground)
                attrs
              }
              else ConsolePane.colorAttributes(console.getPlainColor)
            console.getOutput().writeAttrs(attrs, msg.message.output_text + "\n")
          }
        }
      }
    }

    override def toString: String = super.toString + " plugin"
  }

  val init = """
import isabelle._
import isabelle.jedit._
import isabelle.jedit_main._
val console = isabelle.jedit_main.Scala_Console.running_console()
val view = console.getView()
"""
}

class Scala_Console extends Shell("Scala") {
  /* global state -- owned interpreter thread */

  @volatile private var global_console: Console = null
  @volatile private var global_out: Output = null

  private val console_stream = new OutputStream {
    private def buffer_init(): Bytes.Builder.Stream = new Bytes.Builder.Stream(hint = 100)
    private var buffer = buffer_init()

    override def flush(): Unit = synchronized {
      val str = buffer.builder.done().text
      buffer = buffer_init()
      global_out match {
        case null =>
          java.lang.System.out.print(str)
          java.lang.System.out.flush()
        case out =>
          if (str.nonEmpty) { GUI_Thread.later { out.writeAttrs(null, str) } }
      }
    }

    override def close(): Unit = flush()

    override def write(b: Int): Unit = synchronized {
      buffer.write(b)
      if (b.toChar == '\n') flush()
    }

    override def write(array: Array[Byte], offset: Int, length: Int): Unit = synchronized {
      Objects.checkFromIndexSize(offset, length, array.length)
      for (i <- 0 until length) write(array(offset + i))
    }
  }

  private def with_console[A](console: Console, out: Output)(e: => A): A = {
    global_console = console
    global_out = out
    try {
      scala.Console.withErr(console_stream) {
        scala.Console.withOut(console_stream) { e }
      }
    }
    finally {
      console_stream.flush()
      global_console = null
      global_out = null
    }
  }


  /* jEdit console methods */

  override def openConsole(console: Console): Unit = {
    val context =
      Scala.Compiler.context(
      jar_files = JEdit_Lib.directories,
      class_loader = Some(new JARClassLoader))

    val interpreter = new Scala_Console.Interpreter(context, console)
    interpreter.execute((context, state) =>
      context.compile(Scala_Console.init, state = state).state)
  }

  override def closeConsole(console: Console): Unit =
    Scala_Console.console_interpreter(console).foreach(_.shutdown())

  override def printInfoMessage(out: Output): Unit = {
    out.print(null,
     "This shell evaluates Isabelle/Scala expressions.\n\n" +
     "The contents of package isabelle and isabelle.jedit are imported.\n" +
     "The following special toplevel bindings are provided:\n" +
     "  view    -- current jEdit/Swing view (e.g. view.getBuffer, view.getTextArea)\n" +
     "  console -- jEdit Console plugin (e.g. new Scala_Console.Progress())\n" +
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
      interpreter.execute { (context, state) =>
        val result = with_console(console, out) { context.compile(command, state) }
        GUI_Thread.later {
          val diag = if (err == null) out else err
          for (message <- result.messages) {
            val color = if (message.is_error) console.getErrorColor else null
            diag.print(color, message.text)
          }
          Option(err).foreach(_.commandDone())
          out.commandDone()
        }
        result.state
      })
  }

  override def stop(console: Console): Unit =
    Scala_Console.console_interpreter(console).foreach(_.interrupt_thread())
}
