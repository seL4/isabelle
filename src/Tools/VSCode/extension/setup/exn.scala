/*  Title:      Tools/VSCode/extension/setup/environment.scala
    Author:     Fabian Huch

Isabelle exception handling, written in scala (for JS compilation).
*/

package isabelle.setup

import scala.language.unsafeNulls

import java.io.IOException


object Exn {
  /* interrupts */

  def cause(exn: Throwable): Throwable = {
    var e = exn
    while (e.getCause != null) {
      e = e.getCause
    }
    e
  }

  def is_interrupt(exn: Throwable): Boolean = cause(exn).isInstanceOf[InterruptedException]

  def failure_rc(exn: Throwable): Int = if (is_interrupt(exn)) 130 else 2


  /* message */

  def message(exn: Throwable): String = {
    val msg = exn.getMessage

    if (exn.getClass == classOf[RuntimeException]) {
      if (msg == null || msg.isEmpty) "Error" else msg
    }
    else if (exn.isInstanceOf[IOException]) {
      if (msg == null || msg.isEmpty) "I/O error" else "I/O error: " + msg
    }
    else if (exn.isInstanceOf[RuntimeException] && !msg.isEmpty) msg
    else if (exn.isInstanceOf[InterruptedException]) "Interrupt"
    else exn.toString
  }


  /* print */

  def trace(exn: Throwable): String =
    isabelle.cat_lines(for (elem <- exn.getStackTrace) yield elem.toString)

  def debug(): Boolean = System.getProperty("isabelle.debug", "") == "true"

  def print(exn: Throwable): String =
    if (debug()) message(exn) + "\n" + trace(exn) else message(exn)

  def print_error(exn: Throwable): String = Library.prefix_lines("*** ", print(exn))
}