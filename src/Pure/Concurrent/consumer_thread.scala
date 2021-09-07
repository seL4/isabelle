/*  Title:      Pure/Concurrent/consumer_thread.scala
    Author:     Makarius

Consumer thread with unbounded queueing of requests, and optional
acknowledgment.
*/

package isabelle


import scala.annotation.tailrec


object Consumer_Thread
{
  def fork_bulk[A](name: String = "", daemon: Boolean = false)(
      bulk: A => Boolean,
      consume: List[A] => (List[Exn.Result[Unit]], Boolean),
      finish: () => Unit = () => ()): Consumer_Thread[A] =
    new Consumer_Thread[A](name, daemon, bulk, consume, finish)

  def fork[A](name: String = "", daemon: Boolean = false)(
      consume: A => Boolean,
      finish: () => Unit = () => ()): Consumer_Thread[A] =
  {
    def consume_single(args: List[A]): (List[Exn.Result[Unit]], Boolean) =
    {
      assert(args.length == 1)
      Exn.capture { consume(args.head) } match {
        case Exn.Res(continue) => (List(Exn.Res(())), continue)
        case Exn.Exn(exn) => (List(Exn.Exn(exn)), true)
      }
    }

    fork_bulk(name = name, daemon = daemon)(_ => false, consume_single, finish = finish)
  }
}

final class Consumer_Thread[A] private(
  name: String, daemon: Boolean,
  bulk: A => Boolean,
  consume: List[A] => (List[Exn.Result[Unit]], Boolean),
  finish: () => Unit)
{
  /* thread */

  private var active = true
  private val mailbox = Mailbox[Option[Request]]

  private val thread = Isabelle_Thread.fork(name = name, daemon = daemon) { main_loop(Nil) }
  def is_active: Boolean = active && thread.isAlive
  def check_thread: Boolean = Thread.currentThread == thread

  private def failure(exn: Throwable): Unit =
    Output.error_message(
      "Consumer thread failure: " + quote(thread.getName) + "\n" + Exn.message(exn))

  private def robust_finish(): Unit =
    try { finish() } catch { case exn: Throwable => failure(exn) }


  /* requests */

  private class Request(val arg: A, acknowledge: Boolean = false)
  {
    val ack: Option[Synchronized[Option[Exn.Result[Unit]]]] =
      if (acknowledge) Some(Synchronized(None)) else None

    def await(): Unit =
    {
      for (a <- ack) {
        Exn.release(a.guarded_access({ case None => None case res => Some((res.get, res)) }))
      }
    }
  }

  private def request(req: Request): Unit =
  {
    synchronized {
      if (is_active) mailbox.send(Some(req))
      else error("Consumer thread not active: " + quote(thread.getName))
    }
    req.await()
  }

  @tailrec private def main_loop(msgs: List[Option[Request]]): Unit =
    msgs match {
      case Nil => main_loop(mailbox.receive())
      case None :: _ => robust_finish()
      case _ =>
        val reqs =
          proper_list(msgs.takeWhile(msg => msg.isDefined && bulk(msg.get.arg)))
            .getOrElse(msgs.take(1))
            .map(_.get)

        val (results, continue) = consume(reqs.map(_.arg))

        for { (Some(req), Some(res)) <- reqs.map(Some(_)).zipAll(results.map(Some(_)), None, None) }
        {
          (req.ack, res) match {
            case (Some(a), _) => a.change(_ => Some(res))
            case (None, Exn.Res(_)) =>
            case (None, Exn.Exn(exn)) => failure(exn)
          }
        }

        if (continue) main_loop(msgs.drop(reqs.length))
        else robust_finish()
    }


  /* main methods */

  assert(is_active)

  def send(arg: A): Unit = request(new Request(arg))
  def send_wait(arg: A): Unit = request(new Request(arg, acknowledge = true))

  def shutdown(): Unit =
  {
    synchronized { if (is_active) { active = false; mailbox.send(None) } }
    thread.join()
  }
}
