/*  Title:      Pure/library.scala
    Author:     Makarius

Basic library.
*/

package isabelle

import java.lang.System
import java.awt.Component
import javax.swing.JOptionPane


object Library
{
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

  private def simple_dialog(kind: Int, default_title: String)
    (parent: Component, title: String, message: Any*)
  {
    JOptionPane.showMessageDialog(parent,
      message.toArray.asInstanceOf[Array[AnyRef]],
      if (title == null) default_title else title, kind)
  }

  def dialog = simple_dialog(JOptionPane.PLAIN_MESSAGE, null) _
  def warning_dialog = simple_dialog(JOptionPane.WARNING_MESSAGE, "Warning") _
  def error_dialog = simple_dialog(JOptionPane.ERROR_MESSAGE, "Error") _


  /* timing */

  def timeit[A](message: String)(e: => A) =
  {
    val start = System.currentTimeMillis()
    val result = Exn.capture(e)
    val stop = System.currentTimeMillis()
    System.err.println(
      (if (message.isEmpty) "" else message + " ") + (stop - start) + "ms elapsed time")
    Exn.release(result)
  }
}
