/*  Title:      Pure/General/swing_thread.scala
    Author:     Makarius

Evaluation within the AWT/Swing thread.
*/

package isabelle

import javax.swing.SwingUtilities

object Swing_Thread
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
