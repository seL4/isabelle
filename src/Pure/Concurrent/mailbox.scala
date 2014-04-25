/*  Title:      Pure/Concurrent/mailbox.scala
    Module:     PIDE
    Author:     Makarius

Message exchange via mailbox, with non-blocking send (due to unbounded
queueing) and potentially blocking receive.
*/

package isabelle


import scala.collection.immutable.Queue


object Mailbox
{
  def apply[A]: Mailbox[A] = new Mailbox[A]()
}


class Mailbox[A] private()
{
  private val mailbox = Synchronized(Queue.empty[A])
  override def toString: String = mailbox.value.mkString("Mailbox(", ",", ")")

  def send(msg: A): Unit =
    mailbox.change(_.enqueue(msg))

  def receive: A =
    mailbox.guarded_access(_.dequeueOption)

  def receive_timeout(timeout: Time): Option[A] =
    mailbox.timed_access(_ => Some(Time.now() + timeout), _.dequeueOption)

  def await_empty: Unit =
    mailbox.guarded_access(queue => if (queue.isEmpty) Some(((), queue)) else None)
}
