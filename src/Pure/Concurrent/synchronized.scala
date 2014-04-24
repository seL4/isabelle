/*  Title:      Pure/Concurrent/synchronized.scala
    Module:     PIDE
    Author:     Makarius

Synchronized variables.
*/

package isabelle


object Synchronized
{
  def apply[A](init: A): Synchronized[A] = new Synchronized(init)
}


final class Synchronized[A] private(init: A)
{
  private var state: A = init
  def value: A = synchronized { state }
  def change(f: A => A) = synchronized { state = f(state) }
  def change_result[B](f: A => (B, A)): B = synchronized {
    val (result, new_state) = f(state)
    state = new_state
    result
  }

  override def toString: String = state.toString
}
