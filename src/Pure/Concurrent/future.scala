/*  Title:      Pure/Concurrent/future.scala
    Author:     Makarius

Future values.

Notable differences to scala.actors.Future (as of Scala 2.7.7):

  * We capture/release exceptions as in the ML variant.

  * Future.join works for *any* actor, not just the one of the
    original fork.
*/

package isabelle


import scala.actors.Actor._


object Future
{
  def value[A](x: A): Future[A] = new Finished_Future(x)
  def fork[A](body: => A): Future[A] = new Pending_Future(body)
}

abstract class Future[A]
{
  def peek: Option[Exn.Result[A]]
  def is_finished: Boolean = peek.isDefined
  def join: A
  def map[B](f: A => B): Future[B] = Future.fork { f(join) }

  override def toString =
    peek match {
      case None => "<future>"
      case Some(Exn.Exn(_)) => "<failed>"
      case Some(Exn.Res(x)) => x.toString
    }
}

private class Finished_Future[A](x: A) extends Future[A]
{
  val peek: Option[Exn.Result[A]] = Some(Exn.Res(x))
  val join: A = x
}

private class Pending_Future[A](body: => A) extends Future[A]
{
  @volatile private var result: Option[Exn.Result[A]] = None

  private val evaluator = actor {
    result = Some(Exn.capture(body))
    loop { react { case _ => reply(result.get) } }
  }

  def peek: Option[Exn.Result[A]] = result

  def join: A =
    Exn.release {
      peek match {
        case Some(res) => res
        case None => (evaluator !? ()).asInstanceOf[Exn.Result[A]]
      }
    }
}


