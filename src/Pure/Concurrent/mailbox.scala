/*  Title:      Pure/Concurrent/mailbox.scala
    Author:     Makarius

Message exchange via mailbox, with multiple senders (non-blocking,
unbounded buffering) and single receiver (bulk messages).
*/

package isabelle


object Mailbox {
  def apply[A](limit: Int = 0): Mailbox[A] = new Mailbox[A](limit)
}


class Mailbox[A] private(limit: Int) {
  private val mailbox = Synchronized[List[A]](Nil)
  override def toString: String = mailbox.value.reverse.mkString("Mailbox(", ",", ")")

  def send(msg: A): Unit =
    if (limit <= 0) mailbox.change(msg :: _)
    else mailbox.guarded_access(msgs => if (msgs.length < limit) Some(((), msg :: msgs)) else None)

  def receive(timeout: Option[Time] = None): List[A] =
    (mailbox.timed_access(_ => timeout.map(t => Time.now() + t),
      { case Nil => None case msgs => Some((msgs, Nil)) }) getOrElse Nil).reverse

  def await_empty(): Unit =
    mailbox.guarded_access({ case Nil => Some(((), Nil)) case _ => None })
}
