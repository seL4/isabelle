/*  Title:      Pure/package.scala
    Author:     Makarius

Toplevel isabelle package.
*/

package object isabelle
{
  /* errors */

  object ERROR
  {
    def apply(message: String): Throwable = new RuntimeException(message)
    def unapply(exn: Throwable): Option[String] =
      exn match {
        case e: RuntimeException =>
          val msg = e.getMessage
          Some(if (msg == null) "" else msg)
        case _ => None
      }
  }

  def error(message: String): Nothing = throw ERROR(message)

  def cat_error(msg1: String, msg2: String): Nothing =
    if (msg1 == "") error(msg1)
    else error(msg1 + "\n" + msg2)
}

