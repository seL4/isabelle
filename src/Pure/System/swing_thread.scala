/*  Title:      Pure/System/swing_thread.scala
    Module:     PIDE
    Author:     Makarius
    Author:     Fabian Immler, TU Munich

Evaluation within the AWT/Swing thread.
*/

package isabelle

import javax.swing.{SwingUtilities, Timer}
import java.awt.event.{ActionListener, ActionEvent}


object Swing_Thread
{
  /* checks */

  def assert() = Predef.assert(SwingUtilities.isEventDispatchThread())
  def require() = Predef.require(SwingUtilities.isEventDispatchThread())


  /* main dispatch queue */

  def now[A](body: => A): A =
  {
    if (SwingUtilities.isEventDispatchThread()) body
    else {
      lazy val result = { assert(); Exn.capture(body) }
      SwingUtilities.invokeAndWait(new Runnable { def run = result })
      Exn.release(result)
    }
  }

  def future[A](body: => A): Future[A] =
  {
    if (SwingUtilities.isEventDispatchThread()) Future.value(body)
    else Future.fork { now(body) }
  }

  def later(body: => Unit)
  {
    if (SwingUtilities.isEventDispatchThread()) body
    else SwingUtilities.invokeLater(new Runnable { def run = body })
  }


  /* delayed actions */

  abstract class Delay extends
  {
    def invoke(): Unit
    def revoke(): Unit
    def postpone(time: Time): Unit
  }

  private def delayed_action(first: Boolean)(time: Time)(action: => Unit): Delay =
    new Delay {
      private val timer = new Timer(time.ms.toInt, null)
      timer.setRepeats(false)
      timer.addActionListener(new ActionListener {
        override def actionPerformed(e: ActionEvent) {
          assert()
          timer.setDelay(time.ms.toInt)
          action
        }
      })

      def invoke()
      {
        require()
        if (first) timer.start() else timer.restart()
      }

      def revoke()
      {
        require()
        timer.stop()
        timer.setDelay(time.ms.toInt)
      }

      def postpone(alt_time: Time)
      {
        require()
        if (timer.isRunning) {
          timer.setDelay(timer.getDelay max alt_time.ms.toInt)
          timer.restart()
        }
      }
    }

  // delayed action after first invocation
  def delay_first = delayed_action(true) _

  // delayed action after last invocation
  def delay_last = delayed_action(false) _
}
