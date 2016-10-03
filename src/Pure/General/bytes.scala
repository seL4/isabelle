/*  Title:      Pure/General/bytes.scala
    Module:     PIDE
    Author:     Makarius

Immutable byte vectors versus UTF8 strings.
*/

package isabelle


import java.io.{File => JFile, OutputStream, InputStream, FileInputStream}


object Bytes
{
  val empty: Bytes = new Bytes(Array[Byte](), 0, 0)

  def apply(s: CharSequence): Bytes =
  {
    val str = s.toString
    if (str.isEmpty) empty
    else {
      val b = UTF8.bytes(str)
      new Bytes(b, 0, b.length)
    }
  }

  def apply(a: Array[Byte]): Bytes = apply(a, 0, a.length)

  def apply(a: Array[Byte], offset: Int, length: Int): Bytes =
    if (length == 0) empty
    else {
      val b = new Array[Byte](length)
      System.arraycopy(a, offset, b, 0, length)
      new Bytes(b, 0, b.length)
    }


  /* read */

  def read_stream(stream: InputStream, max_length: Int): Bytes =
  {
    val bytes = new Array[Byte](max_length)
    var i = 0
    var m = 0

    try {
      do {
        m = stream.read(bytes, i, max_length - i)
        if (m != -1) i += m
      } while (m != -1 && max_length > i)
    }
    finally { stream.close }

    new Bytes(bytes, 0, i)
  }

  def read(file: JFile): Bytes =
    read_stream(new FileInputStream(file), file.length.toInt)
}

final class Bytes private(
  protected val bytes: Array[Byte],
  protected val offset: Int,
  val length: Int) extends CharSequence
{
  /* equality */

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


  /* content */

  lazy val sha1_digest: SHA1.Digest = SHA1.digest(bytes)

  override def toString: String =
    UTF8.decode_chars(s => s, bytes, offset, offset + length).toString

  def isEmpty: Boolean = length == 0

  def +(other: Bytes): Bytes =
    if (other.isEmpty) this
    else if (isEmpty) other
    else {
      val new_bytes = new Array[Byte](length + other.length)
      System.arraycopy(bytes, offset, new_bytes, 0, length)
      System.arraycopy(other.bytes, other.offset, new_bytes, length, other.length)
      new Bytes(new_bytes, 0, new_bytes.length)
    }


  /* CharSequence operations */

  def charAt(i: Int): Char =
    if (0 <= i && i < length) (bytes(offset + i).asInstanceOf[Int] & 0xFF).asInstanceOf[Char]
    else throw new IndexOutOfBoundsException

  def subSequence(i: Int, j: Int): Bytes =
  {
    if (0 <= i && i <= j && j <= length) new Bytes(bytes, offset + i, j - i)
    else throw new IndexOutOfBoundsException
  }


  /* write */

  def write(stream: OutputStream): Unit = stream.write(bytes, offset, length)
}

