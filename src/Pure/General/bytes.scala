/*  Title:      Pure/General/bytes.scala
    Module:     PIDE
    Author:     Makarius

Immutable byte vectors versus UTF8 strings.
*/

package isabelle


object Bytes
{
  val empty: Bytes = new Bytes(Array[Byte](), 0, 0)

  def apply(s: CharSequence): Bytes =
  {
    val str = s.toString
    if (str.isEmpty) empty
    else {
      val bytes = UTF8.string_bytes(str)
      new Bytes(bytes, 0, bytes.length)
    }
  }
}

final class Bytes private(
  protected val bytes: Array[Byte],
  protected val offset: Int,
  val length: Int)
{
  /* equality */

  private lazy val hash: Int =
  {
    var h = 0
    for (i <- offset until offset + length) {
      val b = bytes(i).asInstanceOf[Int] & 0xFF
      h = 31 * h + b
    }
    h
  }

  override def hashCode(): Int = hash

  override def equals(that: Any): Boolean =
  {
    that match {
      case other: Bytes =>
        if (this eq other) true
        else if (length != other.length) false
        else (0 until length).forall(i => bytes(offset + i) == other.bytes(other.offset + i))
      case _ => false
    }
  }


  /* content */

  override def toString: String = new String(bytes, offset, length, UTF8.charset)

  def is_empty: Boolean = length == 0

  def +(other: Bytes): Bytes =
    if (other.is_empty) this
    else if (is_empty) other
    else {
      val new_bytes = new Array[Byte](length + other.length)
      java.lang.System.arraycopy(bytes, offset, new_bytes, 0, length)
      java.lang.System.arraycopy(other.bytes, other.offset, new_bytes, length, other.length)
      new Bytes(new_bytes, 0, new_bytes.length)
    }
}

