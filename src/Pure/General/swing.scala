/*  Title:      Pure/General/swing.scala
    Author:     Makarius

Swing utilities.
*/

package isabelle

import javax.swing.SwingUtilities

object Swing
{
  def now(body: => Unit) =
    SwingUtilities.invokeAndWait(new Runnable { def run = body })

  def later(body: => Unit) =
    SwingUtilities.invokeLater(new Runnable { def run = body })
}
