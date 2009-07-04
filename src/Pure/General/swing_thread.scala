/*  Title:      Pure/General/swing_thread.scala
    Author:     Makarius
    Author:     Fabian Immler, TU Munich

Evaluation within the AWT/Swing thread.
*/

package isabelle

import javax.swing.{SwingUtilities, Timer}
import java.awt.event.{ActionListener, ActionEvent}


object Swing_Thread
{
  /* main dispatch queue */

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


  /* delayed actions */

  // turn multiple invocations into single action within time span
  def delay(time_span: Int)(action: => Unit): () => Unit =
  {
    val listener =
      new ActionListener { override def actionPerformed(e: ActionEvent) { action } }
    val timer = new Timer(time_span, listener)
    def invoke()
    {
      if (!timer.isRunning()) {
        timer.setRepeats(false)
        timer.start()
      }
    }
    invoke _
  }
}
