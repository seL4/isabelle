/*  Title:      Pure/library.scala
    Module:     PIDE
    Author:     Makarius

Basic library.
*/

package isabelle


import java.lang.System
import java.util.Locale
import java.util.concurrent.{Future => JFuture, TimeUnit}
import java.awt.{Component, Toolkit}
import javax.swing.JOptionPane

import scala.swing.{ComboBox, TextArea, ScrollPane}
import scala.swing.event.SelectionChanged
import scala.collection.mutable


object Library
{
  /* user errors */

  object ERROR
  {
    def apply(message: String): Throwable = new RuntimeException(message)
    def unapply(exn: Throwable): Option[String] = Exn.user_message(exn)
  }

  def error(message: String): Nothing = throw ERROR(message)

  def cat_error(msg1: String, msg2: String): Nothing =
    if (msg1 == "") error(msg1)
    else error(msg1 + "\n" + msg2)


  /* separated chunks */

  def separate[A](s: A, list: List[A]): List[A] =
    list match {
      case x :: xs if !xs.isEmpty => x :: s :: separate(s, xs)
      case _ => list
    }

  def separated_chunks(sep: Char, source: CharSequence): Iterator[CharSequence] =
    new Iterator[CharSequence] {
      private val end = source.length
      private def next_chunk(i: Int): Option[(CharSequence, Int)] =
      {
        if (i < end) {
          var j = i; do j += 1 while (j < end && source.charAt(j) != sep)
          Some((source.subSequence(i + 1, j), j))
        }
        else None
      }
      private var state: Option[(CharSequence, Int)] = if (end == 0) None else next_chunk(-1)

      def hasNext(): Boolean = state.isDefined
      def next(): CharSequence =
        state match {
          case Some((s, i)) => { state = next_chunk(i); s }
          case None => Iterator.empty.next()
        }
    }

  def space_explode(sep: Char, str: String): List[String] =
    separated_chunks(sep, str).map(_.toString).toList


  /* lines */

  def cat_lines(lines: TraversableOnce[String]): String = lines.mkString("\n")

  def split_lines(str: String): List[String] = space_explode('\n', str)

  def first_line(source: CharSequence): String =
  {
    val lines = separated_chunks('\n', source)
    if (lines.hasNext) lines.next.toString
    else ""
  }


  /* strings */

  def lowercase(str: String): String = str.toLowerCase(Locale.ENGLISH)
  def uppercase(str: String): String = str.toUpperCase(Locale.ENGLISH)

  def capitalize(str: String): String =
    if (str.length == 0) str
    else uppercase(str.substring(0, 1)) + str.substring(1)

  def try_unprefix(prfx: String, s: String): Option[String] =
    if (s.startsWith(prfx)) Some(s.substring(prfx.length)) else None


  /* quote */

  def quote(s: String): String = "\"" + s + "\""
  def commas(ss: Iterable[String]): String = ss.iterator.mkString(", ")
  def commas_quote(ss: Iterable[String]): String = ss.iterator.map(quote).mkString(", ")


  /* reverse CharSequence */

  class Reverse(text: CharSequence, start: Int, end: Int) extends CharSequence
  {
    require(0 <= start && start <= end && end <= text.length)

    def this(text: CharSequence) = this(text, 0, text.length)

    def length: Int = end - start
    def charAt(i: Int): Char = text.charAt(end - i - 1)

    def subSequence(i: Int, j: Int): CharSequence =
      if (0 <= i && i <= j && j <= length) new Reverse(text, end - j, end - i)
      else throw new IndexOutOfBoundsException

    override def toString: String =
    {
      val buf = new StringBuilder(length)
      for (i <- 0 until length)
        buf.append(charAt(i))
      buf.toString
    }
  }


  /* simple dialogs */

  def scrollable_text(txt: String, width: Int = 60, editable: Boolean = false): ScrollPane =
  {
    val text = new TextArea(txt)
    if (width > 0) text.columns = width
    text.editable = editable
    new ScrollPane(text)
  }

  private def simple_dialog(kind: Int, default_title: String,
    parent: Component, title: String, message: Seq[Any])
  {
    Swing_Thread.now {
      val java_message = message map { case x: scala.swing.Component => x.peer case x => x }
      JOptionPane.showMessageDialog(parent,
        java_message.toArray.asInstanceOf[Array[AnyRef]],
        if (title == null) default_title else title, kind)
    }
  }

  def dialog(parent: Component, title: String, message: Any*) =
    simple_dialog(JOptionPane.PLAIN_MESSAGE, null, parent, title, message)

  def warning_dialog(parent: Component, title: String, message: Any*) =
    simple_dialog(JOptionPane.WARNING_MESSAGE, "Warning", parent, title, message)

  def error_dialog(parent: Component, title: String, message: Any*) =
    simple_dialog(JOptionPane.ERROR_MESSAGE, "Error", parent, title, message)

  def confirm_dialog(parent: Component, title: String, option_type: Int, message: Any*): Int =
    Swing_Thread.now {
      val java_message = message map { case x: scala.swing.Component => x.peer case x => x }
      JOptionPane.showConfirmDialog(parent,
        java_message.toArray.asInstanceOf[Array[AnyRef]], title,
          option_type, JOptionPane.QUESTION_MESSAGE)
    }


  /* zoom box */

  class Zoom_Box(apply_factor: Int => Unit) extends ComboBox[String](
    List("50%", "70%", "85%", "100%", "125%", "150%", "175%", "200%", "300%", "400%"))
  {
    val Factor = "([0-9]+)%?".r
    def parse(text: String): Int =
      text match {
        case Factor(s) =>
          val i = Integer.parseInt(s)
          if (10 <= i && i <= 1000) i else 100
        case _ => 100
      }

    def print(i: Int): String = i.toString + "%"

    def set_item(i: Int) {
      peer.getEditor match {
        case null =>
        case editor => editor.setItem(print(i))
      }
    }

    makeEditable()(c => new ComboBox.BuiltInEditor(c)(text => print(parse(text)), x => x))
    reactions += {
      case SelectionChanged(_) => apply_factor(parse(selection.item))
    }
    listenTo(selection)
    selection.index = 3
    prototypeDisplayValue = Some("00000%")
  }


  /* screen resolution */

  def resolution_scale(): Double = Toolkit.getDefaultToolkit.getScreenResolution.toDouble / 72
  def resolution_scale(i: Int): Int = (i.toDouble * resolution_scale()).round.toInt


  /* Java futures */

  def future_value[A](x: A) = new JFuture[A]
  {
    def cancel(may_interrupt: Boolean): Boolean = false
    def isCancelled(): Boolean = false
    def isDone(): Boolean = true
    def get(): A = x
    def get(timeout: Long, time_unit: TimeUnit): A = x
  }
}


class Basic_Library
{
  val ERROR = Library.ERROR
  val error = Library.error _
  val cat_error = Library.cat_error _

  val space_explode = Library.space_explode _
  val split_lines = Library.split_lines _
  val cat_lines = Library.cat_lines _
  val quote = Library.quote _
  val commas = Library.commas _
  val commas_quote = Library.commas_quote _


  /* parallel tasks */

  implicit def function_as_callable[A](f: () => A) =
    new java.util.concurrent.Callable[A] { def call = f() }

  val default_thread_pool =
    scala.collection.parallel.ThreadPoolTasks.defaultThreadPool
}
