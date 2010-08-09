/*  Title:      Pure/library.scala
    Author:     Makarius

Basic library.
*/

package isabelle

import java.lang.System
import java.awt.Component
import javax.swing.JOptionPane


import scala.swing.ComboBox
import scala.swing.event.SelectionChanged


object Library
{
  /* partial functions */

  def undefined[A, B] = new PartialFunction[A, B] {
    def apply(x: A): B = throw new NoSuchElementException("undefined")
    def isDefinedAt(x: A) = false
  }


  /* separate */

  def separate[A](s: A, list: List[A]): List[A] =
    list match {
      case x :: xs if !xs.isEmpty => x :: s :: separate(s, xs)
      case _ => list
    }


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


  /* iterate over chunks (cf. space_explode/split_lines in ML) */

  def chunks(source: CharSequence, sep: Char = '\n') = new Iterator[CharSequence]
  {
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
        case None => throw new NoSuchElementException("next on empty iterator")
      }
  }


  /* simple dialogs */

  private def simple_dialog(kind: Int, default_title: String)
    (parent: Component, title: String, message: Any*)
  {
    Swing_Thread.now {
      val java_message = message map { case x: scala.swing.Component => x.peer case x => x }
      JOptionPane.showMessageDialog(parent,
        java_message.toArray.asInstanceOf[Array[AnyRef]],
        if (title == null) default_title else title, kind)
    }
  }

  def dialog = simple_dialog(JOptionPane.PLAIN_MESSAGE, null) _
  def warning_dialog = simple_dialog(JOptionPane.WARNING_MESSAGE, "Warning") _
  def error_dialog = simple_dialog(JOptionPane.ERROR_MESSAGE, "Error") _


  /* zoom box */

  class Zoom_Box(apply_factor: Int => Unit) extends ComboBox[String](
    List("50%", "70%", "85%", "100%", "125%", "150%", "175%", "200%", "300%", "400%"))
  {
    val Factor = "([0-9]+)%?"r
    def parse(text: String): Int =
      text match {
        case Factor(s) =>
          val i = Integer.parseInt(s)
          if (10 <= i && i <= 1000) i else 100
        case _ => 100
      }
    def print(i: Int): String = i.toString + "%"

    makeEditable()(c => new ComboBox.BuiltInEditor(c)(text => print(parse(text)), x => x))
    reactions += {
      case SelectionChanged(_) => apply_factor(parse(selection.item))
    }
    listenTo(selection)
    selection.index = 3
    prototypeDisplayValue = Some("00000%")
  }


  /* timing */

  def timeit[A](message: String)(e: => A) =
  {
    val start = System.nanoTime()
    val result = Exn.capture(e)
    val stop = System.nanoTime()
    System.err.println(
      (if (message == null || message.isEmpty) "" else message + ": ") +
        ((stop - start).toDouble / 1000000) + "ms elapsed time")
    Exn.release(result)
  }
}
