/*  Title:      Pure/General/bytes.scala
    Author:     Makarius

Immutable byte vectors versus UTF8 strings.
*/

package isabelle


import java.io.{File => JFile, ByteArrayOutputStream, ByteArrayInputStream,
  OutputStream, InputStream, FileInputStream, FileOutputStream}
import java.net.URL
import java.util.Base64

import org.tukaani.xz.{XZInputStream, XZOutputStream}


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

  val newline: Bytes = apply("\n")

  def base64(s: String): Bytes =
  {
    val a = Base64.getDecoder.decode(s)
    new Bytes(a, 0, a.length)
  }


  /* read */

  def read_stream(stream: InputStream, limit: Int = Integer.MAX_VALUE, hint: Int = 1024): Bytes =
    if (limit == 0) empty
    else {
      val out_size = (if (limit == Integer.MAX_VALUE) hint else limit) max 1024
      val out = new ByteArrayOutputStream(out_size)
      val buf = new Array[Byte](8192)
      var m = 0

      do {
        m = stream.read(buf, 0, buf.size min (limit - out.size))
        if (m != -1) out.write(buf, 0, m)
      } while (m != -1 && limit > out.size)

      new Bytes(out.toByteArray, 0, out.size)
    }

  def read(file: JFile): Bytes =
  {
    val length = file.length
    val limit = if (length < 0 || length > Integer.MAX_VALUE) Integer.MAX_VALUE else length.toInt
    using(new FileInputStream(file))(read_stream(_, limit = limit))
  }

  def read(path: Path): Bytes = read(path.file)

  def read(url: URL): Bytes = using(url.openStream)(read_stream(_))


  /* write */

  def write(file: JFile, bytes: Bytes): Unit =
    using(new FileOutputStream(file))(bytes.write_stream(_))

  def write(path: Path, bytes: Bytes): Unit = write(path.file, bytes)
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

  def is_empty: Boolean = length == 0

  def iterator: Iterator[Byte] =
    for (i <- (offset until (offset + length)).iterator)
      yield bytes(i)

  def array: Array[Byte] =
  {
    val a = new Array[Byte](length)
    System.arraycopy(bytes, offset, a, 0, length)
    a
  }

  def text: String =
    UTF8.decode_chars(s => s, bytes, offset, offset + length).toString

  def base64: String =
  {
    val b =
      if (offset == 0 && length == bytes.length) bytes
      else Bytes(bytes, offset, length).bytes
    Base64.getEncoder.encodeToString(b)
  }

  def maybe_base64: (Boolean, String) =
  {
    val s = text
    if (this == Bytes(s)) (false, s) else (true, base64)
  }

  override def toString: String = "Bytes(" + length + ")"

  def proper: Option[Bytes] = if (is_empty) None else Some(this)
  def proper_text: Option[String] = if (is_empty) None else Some(text)

  def +(other: Bytes): Bytes =
    if (other.is_empty) this
    else if (is_empty) other
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

  def trim_line: Bytes =
    if (length >= 2 && charAt(length - 2) == 13 && charAt(length - 1) == 10)
      subSequence(0, length - 2)
    else if (length >= 1 && (charAt(length - 1) == 13 || charAt(length - 1) == 10))
      subSequence(0, length - 1)
    else this


  /* streams */

  def stream(): ByteArrayInputStream = new ByteArrayInputStream(bytes, offset, length)

  def write_stream(stream: OutputStream): Unit = stream.write(bytes, offset, length)


  /* XZ data compression */

  def uncompress(cache: XZ.Cache = XZ.Cache()): Bytes =
    using(new XZInputStream(stream(), cache))(Bytes.read_stream(_, hint = length))

  def compress(options: XZ.Options = XZ.options(), cache: XZ.Cache = XZ.Cache()): Bytes =
  {
    val result = new ByteArrayOutputStream(length)
    using(new XZOutputStream(result, options, cache))(write_stream(_))
    new Bytes(result.toByteArray, 0, result.size)
  }

  def maybe_compress(options: XZ.Options = XZ.options(), cache: XZ.Cache = XZ.Cache())
    : (Boolean, Bytes) =
  {
    val compressed = compress(options = options, cache = cache)
    if (compressed.length < length) (true, compressed) else (false, this)
  }
}
