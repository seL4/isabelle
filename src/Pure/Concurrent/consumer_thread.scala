/*  Title:      Pure/Concurrent/consumer_thread.scala
    Module:     PIDE
    Author:     Makarius

Consumer thread with unbounded queueing of requests.
*/

package isabelle


import scala.annotation.tailrec


object Consumer_Thread
{
  def fork[A](name: String = "", daemon: Boolean = false)(consume: A => Unit): Consumer_Thread[A] =
    new Consumer_Thread[A](name, daemon, consume)
}

final class Consumer_Thread[A] private(name: String, daemon: Boolean, consume: A => Unit)
{
  private var ready = true
  private val mbox = Mailbox[Option[A]]

  @tailrec private def loop(): Unit =
    mbox.receive match {
      case Some(x) => consume(x); loop()
      case None =>
    }
  private val thread = Simple_Thread.fork(name, daemon) { loop() }

  def send(x: A): Unit = synchronized {
    if (ready) mbox.send(Some(x))
    else error("Consumer thread not ready (after shutdown)")
  }

  def shutdown(): Unit =
  {
    synchronized { if (ready) { ready = false; mbox.send(None) } }
    mbox.await_empty
    thread.join
  }
}
