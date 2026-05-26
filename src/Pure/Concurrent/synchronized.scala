/*  Title:      Pure/Concurrent/synchronized.scala
    Author:     Makarius

Synchronized variables.
*/

package isabelle


import scala.annotation.tailrec


object Synchronized {
  def apply[A](init: A): Synchronized[A] = new Synchronized(init)
}


final class Synchronized[A] private(init: A) {
  /* state variable */

  private var state: A = init

  def value: A = synchronized { state }
  override def toString: String = value.toString


  /* synchronized access */

  def timed_access[B](until: A => Option[Time], body: A => Option[(B, A)]): Option[B] =
    synchronized {
      def check(x: A): Option[B] =
        for ((y, x1) <- body(x)) yield {
          state = x1
          notifyAll()
          y
        }
      def min_limit(x: A, a: Option[Time]): Option[Time] = {
        val b = until(x)
        if (b.isEmpty) a
        else if (a.isEmpty) b
        else if (a.get <= b.get) a
        else b
      }
      def wait_until(limit: Option[Time]): Unit =
        limit match {
          case Some(t) => wait((t - Time.now()).ms)
          case None => wait()
        }
      @tailrec def loop(limit0: Option[Time]): Option[B] = {
        val x = state
        check(x) match {
          case None =>
            val limit = min_limit(x, limit0)
            val expired = limit match { case Some(t) => Time.now() >= t case None => false }
            if (expired) None else { wait_until(limit); loop(limit) }
          case some => some
        }
      }
      loop(None)
    }

  def guarded_access[B](body: A => Option[(B, A)]): B =
    timed_access(_ => None, body).get


  /* unconditional change */

  def change(body: A => A): Unit = synchronized { state = body(state); notifyAll() }

  def change_result[B](body: A => (B, A)): B = synchronized {
    val (result, new_state) = body(state)
    state = new_state
    notifyAll()
    result
  }
}
