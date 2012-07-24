/*  Title:      Pure/General/exn.scala
    Module:     PIDE
    Author:     Makarius

Support for exceptions (arbitrary throwables).
*/

package isabelle


object Exn
{
  /* exceptions as values */

  sealed abstract class Result[A]
  case class Res[A](res: A) extends Result[A]
  case class Exn[A](exn: Throwable) extends Result[A]

  def capture[A](e: => A): Result[A] =
    try { Res(e) }
    catch { case exn: Throwable => Exn[A](exn) }

  def release[A](result: Result[A]): A =
    result match {
      case Res(x) => x
      case Exn(exn) => throw exn
    }


  /* message */

  private val runtime_exception = Class.forName("java.lang.RuntimeException")

  def user_message(exn: Throwable): Option[String] =
    if (exn.isInstanceOf[java.io.IOException]) {
      val msg = exn.getMessage
      Some(if (msg == null) "I/O error" else "I/O error: " + msg)
    }
    else if (exn.getClass == runtime_exception) {
      val msg = exn.getMessage
      Some(if (msg == null) "Error" else msg)
    }
    else if (exn.isInstanceOf[RuntimeException]) Some(exn.toString)
    else None

  def message(exn: Throwable): String =
    user_message(exn) getOrElse exn.toString
}

