/*  Title:      Pure/Concurrent/consumer_thread.scala
    Author:     Makarius

Consumer thread with unbounded queueing of requests, and optional
acknowledgment.
*/

package isabelle


import scala.annotation.tailrec


object Consumer_Thread
{
  def fork[A](name: String = "", daemon: Boolean = false)(
      consume: A => Boolean,
      finish: () => Unit = () => ()): Consumer_Thread[A] =
    new Consumer_Thread[A](name, daemon, consume, finish)
}

final class Consumer_Thread[A] private(
  name: String, daemon: Boolean, consume: A => Boolean, finish: () => Unit)
{
  /* thread */

  private var active = true
  private val mailbox = Mailbox[Option[Request]]

  private val thread = Standard_Thread.fork(name, daemon) { main_loop(Nil) }
  def is_active: Boolean = active && thread.isAlive
  def check_thread: Boolean = Thread.currentThread == thread

  private def failure(exn: Throwable): Unit =
    Output.error_message(
      "Consumer thread failure: " + quote(thread.getName) + "\n" + Exn.message(exn))

  private def robust_finish(): Unit =
    try { finish() } catch { case exn: Throwable => failure(exn) }


  /* requests */

  private class Request(arg: A, acknowledge: Boolean = false)
  {
    private val ack: Option[Synchronized[Option[Exn.Result[Unit]]]] =
      if (acknowledge) Some(Synchronized(None)) else None

    def apply: Boolean =
    {
      val result = Exn.capture { consume(arg) }
      (ack, result) match {
        case ((Some(a), _)) => a.change(_ => Some(result.map(_ => ())))
        case ((None, Exn.Res(_))) =>
        case ((None, Exn.Exn(exn))) => failure(exn)
      }
      result match {
        case Exn.Res(continue) => continue
        case Exn.Exn(_) => true
      }
    }

    def await
    {
      for (a <- ack) {
        Exn.release(a.guarded_access({ case None => None case res => Some((res.get, res)) }))
      }
    }
  }

  private def request(req: Request)
  {
    synchronized {
      if (is_active) mailbox.send(Some(req))
      else error("Consumer thread not active: " + quote(thread.getName))
    }
    req.await
  }

  @tailrec private def main_loop(msgs: List[Option[Request]]): Unit =
    msgs match {
      case Nil => main_loop(mailbox.receive(None))
      case Some(req) :: rest =>
        val continue = req.apply
        if (continue) main_loop(rest) else robust_finish()
      case None :: _ => robust_finish()
    }


  /* main methods */

  assert(is_active)

  def send(arg: A) { request(new Request(arg)) }
  def send_wait(arg: A) { request(new Request(arg, acknowledge = true)) }

  def shutdown()
  {
    synchronized { if (is_active) { active = false; mailbox.send(None) } }
    thread.join
  }
}
