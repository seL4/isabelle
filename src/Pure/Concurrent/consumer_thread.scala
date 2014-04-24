/*  Title:      Pure/Concurrent/consumer_thread.scala
    Module:     PIDE
    Author:     Makarius

Consumer thread with unbounded queueing of requests.
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
  private var active = true
  private val mbox = Mailbox[Option[A]]

  private def failure(exn: Throwable): Unit =
    System.err.println("Consumer thread failure:\n" + Exn.message(exn))

  private def robust_finish(): Unit =
    try { finish() } catch { case exn: Throwable => failure(exn) }

  @tailrec private def loop(): Unit =
    mbox.receive match {
      case Some(x) =>
        val continue =
          try { consume(x) }
          catch { case exn: Throwable => failure(exn); true }
        if (continue) loop() else robust_finish()
      case None => robust_finish()
    }
  private val thread = Simple_Thread.fork(name, daemon) { loop() }

  private def is_active: Boolean = active && thread.isAlive


  /* main methods */

  def send(x: A): Unit = synchronized {
    if (is_active) mbox.send(Some(x))
    else error("Consumer thread not active")
  }

  def shutdown(): Unit =
  {
    synchronized { if (is_active) { active = false; mbox.send(None) } }
    thread.join
  }
}
