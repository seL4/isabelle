/*  Title:      Pure/General/exn.scala
    Author:     Makarius

Support for exceptions (arbitrary throwables).
*/

package isabelle


object Exn
{
  /* user errors */

  class User_Error(message: String) extends RuntimeException(message)
  {
    override def equals(that: Any): Boolean =
      that match {
        case other: User_Error => message == other.getMessage
        case _ => false
      }
    override def hashCode: Int = message.hashCode

    override def toString: String = "\n" + Output.error_message_text(message)
  }

  object ERROR
  {
    def apply(message: String): User_Error = new User_Error(message)
    def unapply(exn: Throwable): Option[String] = user_message(exn)
  }

  def error(message: String): Nothing = throw ERROR(message)

  def cat_message(msgs: String*): String =
    cat_lines(msgs.iterator.filterNot(_ == ""))

  def cat_error(msgs: String*): Nothing =
    error(cat_message(msgs:_*))


  /* exceptions as values */

  sealed abstract class Result[A]
  {
    def user_error: Result[A] =
      this match {
        case Exn(ERROR(msg)) => Exn(ERROR(msg))
        case _ => this
      }

    def map[B](f: A => B): Result[B] =
      this match {
        case Res(res) => Res(f(res))
        case Exn(exn) => Exn(exn)
      }
  }
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

  def release_first[A](results: List[Result[A]]): List[A] =
    results.find({ case Exn(exn) => !is_interrupt(exn) case _ => false }) match {
      case Some(Exn(exn)) => throw exn
      case _ => results.map(release)
    }


  /* interrupts */

  def is_interrupt(exn: Throwable): Boolean =
    isabelle.setup.Exn.is_interrupt(exn)

  def failure_rc(exn: Throwable): Int =
    isabelle.setup.Exn.failure_rc(exn)

  def interruptible_capture[A](e: => A): Result[A] =
    try { Res(e) }
    catch { case exn: Throwable if !is_interrupt(exn) => Exn[A](exn) }

  object Interrupt
  {
    object ERROR
    {
      def unapply(exn: Throwable): Option[String] =
        if (is_interrupt(exn)) Some(message(exn)) else user_message(exn)
    }

    def apply(): Throwable = new InterruptedException("Interrupt")
    def unapply(exn: Throwable): Boolean = is_interrupt(exn)

    def dispose(): Unit = Thread.interrupted()
    def expose(): Unit = if (Thread.interrupted()) throw apply()
    def impose(): Unit = Thread.currentThread.interrupt()
  }


  /* message */

  def user_message(exn: Throwable): Option[String] =
    if (exn.isInstanceOf[User_Error] || exn.getClass == classOf[RuntimeException])
    {
      Some(proper_string(exn.getMessage) getOrElse "Error")
    }
    else if (exn.isInstanceOf[java.sql.SQLException])
    {
      Some(proper_string(exn.getMessage) getOrElse "SQL error")
    }
    else if (exn.isInstanceOf[java.io.IOException])
    {
      val msg = exn.getMessage
      Some(if (msg == null || msg == "") "I/O error" else "I/O error: " + msg)
    }
    else if (exn.isInstanceOf[RuntimeException]) Some(exn.toString)
    else None

  def message(exn: Throwable): String =
    user_message(exn) getOrElse (if (is_interrupt(exn)) "Interrupt" else exn.toString)


  /* print */

  def debug(): Boolean = isabelle.setup.Exn.debug()

  def trace(exn: Throwable): String = isabelle.setup.Exn.trace(exn)

  def print(exn: Throwable): String =
    if (debug()) message(exn) + "\n" + trace(exn) else message(exn)
}
