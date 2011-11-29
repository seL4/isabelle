/*  Title:      Pure/Concurrent/future.scala
    Module:     Library
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
  def promise[A]: Promise[A] = new Promise_Future
}

abstract class Future[A]
{
  def peek: Option[Exn.Result[A]]
  def is_finished: Boolean = peek.isDefined
  def get_finished: A = { require(is_finished); Exn.release(peek.get) }
  def join: A
  def map[B](f: A => B): Future[B] = Future.fork { f(join) }

  override def toString =
    peek match {
      case None => "<future>"
      case Some(Exn.Exn(_)) => "<failed>"
      case Some(Exn.Res(x)) => x.toString
    }
}

abstract class Promise[A] extends Future[A]
{
  def fulfill_result(res: Exn.Result[A]): Unit
  def fulfill(x: A) { fulfill_result(Exn.Res(x)) }
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

private class Promise_Future[A] extends Promise[A]
{
  @volatile private var result: Option[Exn.Result[A]] = None

  private case object Read
  private case class Write(res: Exn.Result[A])

  private val receiver = actor {
    loop {
      react {
        case Read if result.isDefined => reply(result.get)
        case Write(res) =>
          if (result.isDefined) reply(false)
          else { result = Some(res); reply(true) }
      }
    }
  }

  def peek: Option[Exn.Result[A]] = result

  def join: A =
    Exn.release {
      result match {
        case Some(res) => res
        case None => (receiver !? Read).asInstanceOf[Exn.Result[A]]
      }
    }

  def fulfill_result(res: Exn.Result[A]) {
    receiver !? Write(res) match {
      case false => error("Duplicate fulfillment of promise")
      case _ =>
    }
  }
}

