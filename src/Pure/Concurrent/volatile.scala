/*  Title:      Pure/Concurrent/volatile.scala
    Module:     PIDE
    Author:     Makarius

Volatile variables.
*/

package isabelle


object Volatile
{
  def apply[A](init: A): Volatile[A] = new Volatile(init)
}


final class Volatile[A] private(init: A)
{
  @volatile private var state: A = init
  def value: A = state
  def change(f: A => A) { state = f(state) }
  def change_result[B](f: A => (B, A)): B =
  {
    val (result, new_state) = f(state)
    state = new_state
    result
  }

  override def toString: String = state.toString
}

