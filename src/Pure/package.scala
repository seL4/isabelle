/*  Title:      Pure/package.scala
    Author:     Makarius

Toplevel isabelle package.
*/

package object isabelle
{
  def error(message: String): Nothing = throw new RuntimeException(message)
}

