/*  Title:      Pure/General/swing_thread.scala
    Author:     Makarius
    Author:     Fabian Immler, TU Munich

Evaluation within the AWT/Swing thread.
*/

package isabelle

import javax.swing.{SwingUtilities, Timer}
import java.awt.event.{ActionListener, ActionEvent}

import scala.actors.{Future, Futures}


object Swing_Thread
{
  /* checks */

  def assert() = Predef.assert(SwingUtilities.isEventDispatchThread())
  def require() = Predef.require(SwingUtilities.isEventDispatchThread())


  /* main dispatch queue */

  def now[A](body: => A): A =
  {
    var result: Option[A] = None
    if (SwingUtilities.isEventDispatchThread()) { result = Some(body) }
    else SwingUtilities.invokeAndWait(new Runnable { def run = { result = Some(body) } })
    result.get
  }

  def future[A](body: => A): Future[A] =
    Futures.future(now(body))

  def later(body: => Unit) {
    if (SwingUtilities.isEventDispatchThread()) body
    else SwingUtilities.invokeLater(new Runnable { def run = body })
  }


  /* delayed actions */

  private def delayed_action(first: Boolean)(time_span: Int)(action: => Unit): () => Unit =
  {
    val listener =
      new ActionListener { override def actionPerformed(e: ActionEvent) { action } }
    val timer = new Timer(time_span, listener)
    timer.setRepeats(false)

    def invoke() { if (first) timer.start() else timer.restart() }
    invoke _
  }

  // delayed action after first invocation
  def delay_first = delayed_action(true) _

  // delayed action after last invocation
  def delay_last = delayed_action(false) _
}
