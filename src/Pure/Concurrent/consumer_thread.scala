/*  Title:      Pure/Concurrent/consumer_thread.scala
    Module:     PIDE
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


  /* internal messages */

  private type Ack = Synchronized[Option[Exn.Result[Boolean]]]
  private type Request[A] = (A, Option[Ack])
}

final class Consumer_Thread[A] private(
  name: String, daemon: Boolean, consume: A => Boolean, finish: () => Unit)
{
  private var active = true
  private val mbox = Mailbox[Option[Consumer_Thread.Request[A]]]

  private val thread = Simple_Thread.fork(name, daemon) { main_loop() }
  def is_active: Boolean = active && thread.isAlive

  private def failure(exn: Throwable): Unit =
    Output.error_message(
      "Consumer thread failure: " + quote(thread.getName) + "\n" + Exn.message(exn))

  private def robust_finish(): Unit =
    try { finish() } catch { case exn: Throwable => failure(exn) }

  @tailrec private def main_loop(): Unit =
    mbox.receive match {
      case Some((arg, ack)) =>
        val result = Exn.capture { consume(arg) }
        val continue =
          result match {
            case Exn.Res(cont) => cont
            case Exn.Exn(exn) =>
              if (!ack.isDefined) failure(exn)
              true
          }
        ack.foreach(a => a.change(_ => Some(result)))
        if (continue) main_loop() else robust_finish()
      case None => robust_finish()
    }

  assert(is_active)


  /* main methods */

  private def request(x: A, ack: Option[Consumer_Thread.Ack])
  {
    synchronized {
      if (is_active) mbox.send(Some((x, ack)))
      else error("Consumer thread not active: " + quote(thread.getName))
    }
    ack.foreach(a =>
      Exn.release(a.guarded_access({ case None => None case res => Some((res.get, res)) })))
  }

  def send(arg: A) { request(arg, None) }
  def send_wait(arg: A) { request(arg, Some(Synchronized(None))) }

  def shutdown(): Unit =
  {
    synchronized { if (is_active) { active = false; mbox.send(None) } }
    thread.join
  }
}
