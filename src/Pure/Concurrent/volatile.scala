/*  Title:      Pure/Concurrent/volatile.scala
    Module:     Library
    Author:     Makarius

Volatile variables.
*/

package isabelle


object Volatile
{
  def apply[A](init: A): Volatile[A] = new Volatile(init)
}


class Volatile[A] private(init: A)
{
  @volatile private var state: A = init
  def apply(): A = state
  def change(f: A => A) { state = f(state) }
  def change_yield[B](f: A => (B, A)): B =
  {
    val (result, new_state) = f(state)
    state = new_state
    result
  }
}

