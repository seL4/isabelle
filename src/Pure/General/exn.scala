/*  Title:      Pure/General/exn.scala
    Module:     Library
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

  def message(exn: Throwable): String =
    if (exn.getClass == runtime_exception) {
      val msg = exn.getMessage
      if (msg == null) "Error" else msg
    }
    else exn.toString
}

