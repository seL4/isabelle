/*  Title:      Pure/General/swing.scala
    Author:     Makarius

Swing utilities.
*/

package isabelle

import javax.swing.SwingUtilities

object Swing
{
  def now(body: => Unit) {
    if (SwingUtilities.isEventDispatchThread) body
    else SwingUtilities.invokeAndWait(new Runnable { def run = body })
  }

  def later(body: => Unit) {
    if (SwingUtilities.isEventDispatchThread) body
    else SwingUtilities.invokeLater(new Runnable { def run = body })
  }
}
