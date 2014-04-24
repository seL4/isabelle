/*  Title:      Pure/Concurrent/consumer_thread.scala
    Module:     PIDE
    Author:     Makarius

Consumer thread with unbounded queueing of requests.
*/

package isabelle


import scala.annotation.tailrec


class Consumer_Thread[A](name: String = "", daemon: Boolean = false)
{
  def consume(x: A) { }
  def finish() { }

  private val mbox = Mailbox[Option[A]]
  @tailrec private def loop(): Unit =
    mbox.receive match {
      case Some(x) => consume(x); loop()
      case None => finish()
    }
  private val thread = Simple_Thread.fork(name, daemon) { loop() }

  final def send(x: A) { mbox.send(Some(x)) }
  final def shutdown() { mbox.send(None); mbox.await_empty; thread.join }
}
