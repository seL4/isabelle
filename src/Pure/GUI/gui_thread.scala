/*  Title:      Pure/GUI/gui_thread.scala
    Author:     Makarius

Evaluation within the GUI thread (for AWT/Swing).
*/

package isabelle


import javax.swing.SwingUtilities


object GUI_Thread
{
  /* context check */

  def assert[A](body: => A): A =
  {
    Predef.assert(SwingUtilities.isEventDispatchThread())
    body
  }

  def require[A](body: => A): A =
  {
    Predef.require(SwingUtilities.isEventDispatchThread())
    body
  }


  /* event dispatch queue */

  def now[A](body: => A): A =
  {
    if (SwingUtilities.isEventDispatchThread()) body
    else {
      lazy val result = { assert { Exn.capture(body) } }
      SwingUtilities.invokeAndWait(new Runnable { def run = result })
      Exn.release(result)
    }
  }

  def later(body: => Unit)
  {
    if (SwingUtilities.isEventDispatchThread()) body
    else SwingUtilities.invokeLater(new Runnable { def run = body })
  }

  def future[A](body: => A): Future[A] =
  {
    if (SwingUtilities.isEventDispatchThread()) Future.value(body)
    else {
      val promise = Future.promise[A]
      later { promise.fulfill_result(Exn.capture(body)) }
      promise
    }
  }


  /* delayed events */

  def delay_first(delay: => Time)(event: => Unit): Standard_Thread.Delay =
    Standard_Thread.delay_first(delay) { later { event } }

  def delay_last(delay: => Time)(event: => Unit): Standard_Thread.Delay =
    Standard_Thread.delay_last(delay) { later { event } }
}
