/*  Title:      Pure/General/space.scala
    Author:     Makarius

Storage space based on bytes.
*/

package isabelle


object Space {
  def bytes(bs: Long): Space = new Space(bs)
  val zero: Space = bytes(0L)
}

final class Space private(val bytes: Long) extends AnyVal {
  override def toString: String = bytes.toString
}
