/*  Title:      Pure/System/jfx_thread.scala
    Module:     PIDE
    Author:     Makarius

Evaluation within the Java FX application thread.
*/

package isabelle

import javafx.application.{Platform => JFX_Platform}


object JFX_Thread
{
  /* checks */

  def assert() = Predef.assert(JFX_Platform.isFxApplicationThread())
  def require() = Predef.require(JFX_Platform.isFxApplicationThread())


  /* asynchronous context switch */

  def later(body: => Unit)
  {
    if (JFX_Platform.isFxApplicationThread()) body
    else JFX_Platform.runLater(new Runnable { def run = body })
  }
}
