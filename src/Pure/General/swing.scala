/*  Title:      Pure/General/swing.scala
    Author:     Makarius

Swing utilities.
*/

package isabelle

import javax.swing.SwingUtilities

object Swing
{
  def now[A](body: => A): A = {
    var result: Option[A] = None
    if (SwingUtilities.isEventDispatchThread) { result = Some(body) }
    else SwingUtilities.invokeAndWait(new Runnable { def run = { result = Some(body) } })
    result.get
  }

  def later(body: => Unit) {
    if (SwingUtilities.isEventDispatchThread) body
    else SwingUtilities.invokeLater(new Runnable { def run = body })
  }
}
