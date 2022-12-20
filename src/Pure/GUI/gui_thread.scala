/*  Title:      Pure/GUI/gui_thread.scala
    Author:     Makarius

Evaluation within the GUI thread (for AWT/Swing).
*/

package isabelle


import javax.swing.SwingUtilities


object GUI_Thread {
  /* context check */

  def check(): Boolean = SwingUtilities.isEventDispatchThread()

  def assert[A](body: => A): A = {
    Predef.assert(check())
    body
  }

  def require[A](body: => A): A = {
    Predef.require(check(), "GUI thread expected")
    body
  }


  /* event dispatch queue */

  def now[A](body: => A): A = {
    if (check()) body
    else {
      lazy val result = assert { Exn.capture(body) }
      SwingUtilities.invokeAndWait(() => result)
      Exn.release(result)
    }
  }

  def later(body: => Unit): Unit = {
    if (check()) body
    else SwingUtilities.invokeLater(() => body)
  }

  def future[A](body: => A): Future[A] = {
    if (check()) Future.value(body)
    else {
      val promise = Future.promise[A]
      later { promise.fulfill_result(Exn.capture(body)) }
      promise
    }
  }
}
