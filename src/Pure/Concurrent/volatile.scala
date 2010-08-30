/*  Title:      Pure/Concurrent/volatile.scala
    Author:     Makarius

Volatile variables.
*/

package isabelle


class Volatile[A](init: A)
{
  @volatile private var state: A = init
  def peek(): A = state
  def change(f: A => A) { state = f(state) }
  def change_yield[B](f: A => (B, A)): B =
  {
    val (result, new_state) = f(state)
    state = new_state
    result
  }
}

