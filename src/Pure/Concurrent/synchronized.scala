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
        body(x) match {
          case None => None
          case Some((y, x1)) =>
            state = x1
            notifyAll()
            Some(y)
        }
      @tailrec def loop(): Option[B] = {
        val x = state
        check(x) match {
          case None =>
            until(x) match {
              case Some(t) =>
                Time.now() match {
                  case now if t > now =>
                    wait((t - now).ms)
                    check(state)
                  case _ => None
                }
              case None =>
                wait()
                loop()
            }
          case some => some
        }
      }
      loop()
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
