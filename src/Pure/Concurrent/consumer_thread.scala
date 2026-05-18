/*  Title:      Pure/Concurrent/consumer_thread.scala
    Author:     Makarius

Consumer thread with unbounded queueing of requests, and optional
acknowledgment.
*/

package isabelle


import scala.annotation.tailrec


object Consumer_Thread {
  def fork_bulk[A](
    name: String,
    consume: List[A] => (List[Exn.Result[Unit]], Boolean),
    bulk: A => Boolean = (_: A) => true,
    daemon: Boolean = false,
    timeout: Option[Time] = None,
    limit: Int = 0,
    finish: () => Unit = () => (),
    log: Logger = new Console_Logger()
  ): Consumer_Thread[A] = {
    new Consumer_Thread[A](name, consume, bulk, daemon, timeout, limit, finish, log)
  }

  def fork[A](
    name: String,
    consume: A => Boolean,
    daemon: Boolean = false,
    limit: Int = 0,
    finish: () => Unit = () => (),
    log: Logger = new Console_Logger()
  ): Consumer_Thread[A] = {
    fork_bulk(name, bulk = _ => false, daemon = daemon, limit = limit, finish = finish, log = log,
      consume = { (args: List[A]) =>
        assert(args.length == 1)
        Exn.capture { consume(args.head) } match {
          case Exn.Res(cont) => (List(Exn.Res(())), cont)
          case Exn.Exn(exn) => (List(Exn.Exn(exn)), true)
        }
      }
    )
  }
}

final class Consumer_Thread[A] private(
  name: String,
  consume: List[A] => (List[Exn.Result[Unit]], Boolean),
  bulk: A => Boolean,
  daemon: Boolean,
  timeout: Option[Time],
  limit: Int,
  finish: () => Unit,
  log: Logger
) {
  /* thread */

  private var active = true
  private val mailbox = Mailbox[Option[Request]](limit = limit)

  private val thread = Isabelle_Thread.fork(name = name, daemon = daemon) { main_loop(Nil) }
  private def thread_name: String = proper_string(thread.getName).getOrElse("")
  def is_active(): Boolean = active && thread.isAlive
  def check_thread(): Boolean = Isabelle_Thread.current == thread

  private def failure(exn: Throwable): Unit =
    log.error_message("Consumer thread failure: " + quote(thread_name) + "\n" + Exn.print(exn))

  private def robust_finish(): Unit =
    try { finish() } catch { case exn: Throwable => failure(exn) }


  /* requests */

  private class Request(val arg: A, acknowledge: Boolean = false) {
    val ack: Option[Synchronized[Option[Exn.Result[Unit]]]] =
      if (acknowledge) Some(Synchronized(None)) else None

    def await(): Unit = {
      for (a <- ack) {
        Exn.release(a.guarded_access({ case None => None case res => Some((res.get, res)) }))
      }
    }
  }

  private def request(req: Request): Unit = {
    synchronized {
      if (is_active()) mailbox.send(Some(req))
      else error("Consumer thread not active: " + quote(thread_name))
    }
    req.await()
  }

  private def process(msgs: List[Option[Request]]): (List[Option[Request]], Boolean) = {
    val reqs =
      proper_list(msgs.takeWhile(msg => msg.isDefined && bulk(msg.get.arg)))
        .getOrElse(msgs.take(1))
        .map(_.get)
    val rest = msgs.drop(reqs.length)

    val (results, cont) = consume(reqs.map(_.arg))
    for {
      case (Some(req), Some(res)) <- reqs.map(Some(_)).zipAll(results.map(Some(_)), None, None)
    } {
      (req.ack, res) match {
        case (Some(a), _) => a.change(_ => Some(res))
        case (None, Exn.Res(_)) =>
        case (None, Exn.Exn(exn)) => failure(exn)
      }
    }

    (rest, cont)
  }

  @tailrec private def main_loop(buffer: List[Option[Request]]): Unit =
    proper_list(buffer).getOrElse(mailbox.receive(timeout = timeout)) match {
      case None :: _ => robust_finish()
      case msgs =>
        val (rest, cont) = process(msgs)
        if (cont) main_loop(rest) else robust_finish()
    }


  /* main methods */

  assert(is_active())

  def send(arg: A): Unit = request(new Request(arg))
  def send_wait(arg: A): Unit = request(new Request(arg, acknowledge = true))

  def shutdown(): Unit = {
    synchronized { if (is_active()) { active = false; mailbox.send(None) } }
    thread.join()
  }
}
