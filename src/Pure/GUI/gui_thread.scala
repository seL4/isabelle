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
    Predef.assert(SwingUtilities.isEventDispatchThread)
    body
  }

  def require[A](body: => A): A =
  {
    Predef.require(SwingUtilities.isEventDispatchThread, "GUI thread expected")
    body
  }


  /* event dispatch queue */

  def now[A](body: => A): A =
  {
    if (SwingUtilities.isEventDispatchThread) body
    else {
      lazy val result = assert { Exn.capture(body) }
      SwingUtilities.invokeAndWait(() => result)
      Exn.release(result)
    }
  }

  def later(body: => Unit): Unit =
  {
    if (SwingUtilities.isEventDispatchThread) body
    else SwingUtilities.invokeLater(() => body)
  }

  def future[A](body: => A): Future[A] =
  {
    if (SwingUtilities.isEventDispatchThread) Future.value(body)
    else {
      val promise = Future.promise[A]
      later { promise.fulfill_result(Exn.capture(body)) }
      promise
    }
  }
}
