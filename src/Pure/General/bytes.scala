/*  Title:      Pure/General/bytes.scala
    Author:     Makarius

Immutable byte vectors versus UTF8 strings.
*/

package isabelle


import java.io.{ByteArrayInputStream, ByteArrayOutputStream, FileInputStream, FileOutputStream,
  InputStream, OutputStream, File => JFile}
import java.nio.ByteBuffer
import java.nio.channels.FileChannel
import java.nio.file.StandardOpenOption
import java.util.Arrays
import org.tukaani.xz
import com.github.luben.zstd


object Bytes {
  val empty: Bytes = new Bytes(Array[Byte](), 0, 0)

  def apply(s: CharSequence): Bytes = {
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


  /* base64 */

  def decode_base64(s: String): Bytes = {
    val a = Base64.decode(s)
    new Bytes(a, 0, a.length)
  }


  /* read */

  def read_stream(stream: InputStream, limit: Int = Int.MaxValue, hint: Int = 1024): Bytes =
    if (limit == 0) empty
    else {
      val out_size = (if (limit == Int.MaxValue) hint else limit) max 1024
      val out = new ByteArrayOutputStream(out_size)
      val buf = new Array[Byte](8192)
      var m = 0

      while ({
        m = stream.read(buf, 0, buf.length min (limit - out.size))
        if (m != -1) out.write(buf, 0, m)
        m != -1 && limit > out.size
      }) ()

      new Bytes(out.toByteArray, 0, out.size)
    }

  def read_url(name: String): Bytes = using(Url(name).open_stream())(read_stream(_))

  def read_file(path: Path, offset: Long = 0L, limit: Long = Long.MaxValue): Bytes = {
    val length = File.size(path)
    val start = offset.max(0L)
    val len = (length - start).max(0L).min(limit)
    if (len > Int.MaxValue) error("Cannot read large file slice: " + Space.bytes(len).print)
    else if (len == 0L) empty
    else {
      using(FileChannel.open(path.java_path, StandardOpenOption.READ)) { java_path =>
        java_path.position(start)
        val n = len.toInt
        val buf = ByteBuffer.allocate(n)
        var i = 0
        var m = 0
        while ({
          m = java_path.read(buf)
          if (m != -1) i += m
          m != -1 && n > i
        }) ()
        new Bytes(buf.array, 0, i)
      }
    }
  }

  def read(path: Path): Bytes = read_file(path)
  def read(file: JFile): Bytes = read_file(File.path(file))


  /* write */

  def write(file: JFile, bytes: Bytes): Unit =
    using(new FileOutputStream(file))(bytes.write_stream(_))

  def write(path: Path, bytes: Bytes): Unit = write(path.file, bytes)


  /* append */

  def append(file: JFile, bytes: Bytes): Unit =
    using(new FileOutputStream(file, true))(bytes.write_stream(_))

  def append(path: Path, bytes: Bytes): Unit = append(path.file, bytes)


  /* vector of short unsigned integers */

  trait Vec {
    def size: Long
    def apply(i: Long): Char
  }

  class Vec_String(string: String) extends Vec {
    override def size: Long = string.length.toLong
    override def apply(i: Long): Char =
      if (0 <= i && i < size) string(i.toInt)
      else throw new IndexOutOfBoundsException
  }
}

final class Bytes private(
  protected val bytes: Array[Byte],
  protected val offset: Int,
  val length: Int) extends Bytes.Vec {
  /* equality */

  override def equals(that: Any): Boolean = {
    that match {
      case other: Bytes =>
        this.eq(other) ||
        Arrays.equals(bytes, offset, offset + length,
          other.bytes, other.offset, other.offset + other.length)
      case _ => false
    }
  }

  private lazy val hash: Int = {
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

  def array: Array[Byte] = {
    val a = new Array[Byte](length)
    System.arraycopy(bytes, offset, a, 0, length)
    a
  }

  def text: String =
    if (is_empty) ""
    else if (iterator.forall((b: Byte) => b >= 0)) {
      new String(bytes, offset, length, UTF8.charset)
    }
    else UTF8.decode_permissive_bytes(this)

  def wellformed_text: Option[String] = {
    val s = text
    if (this == Bytes(s)) Some(s) else None
  }

  def encode_base64: String = {
    val b =
      if (offset == 0 && length == bytes.length) bytes
      else Bytes(bytes, offset, length).bytes
    Base64.encode(b)
  }

  def maybe_encode_base64: (Boolean, String) =
    wellformed_text match {
      case Some(s) => (false, s)
      case None => (true, encode_base64)
    }

  override def toString: String =
    if (is_empty) "Bytes.empty" else "Bytes(" + Space.bytes(length).print + ")"

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


  /* Vec operations */

  def size: Long = length.toLong

  def apply(i: Long): Char =
    if (0 <= i && i < size) (bytes((offset + i).toInt).asInstanceOf[Int] & 0xFF).asInstanceOf[Char]
    else throw new IndexOutOfBoundsException


  /* slice */

  def slice(i: Long, j: Long): Bytes =
    if (0 <= i && i <= j && j <= size) new Bytes(bytes, (offset + i).toInt, (j - i).toInt)
    else throw new IndexOutOfBoundsException

  def trim_line: Bytes =
    if (size >= 2 && apply(size - 2) == 13 && apply(size - 1) == 10) {
      slice(0, size - 2)
    }
    else if (size >= 1 && (apply(size - 1) == 13 || apply(size - 1) == 10)) {
      slice(0, size - 1)
    }
    else this


  /* streams */

  def stream(): ByteArrayInputStream = new ByteArrayInputStream(bytes, offset, length)

  def write_stream(stream: OutputStream): Unit = stream.write(bytes, offset, length)


  /* XZ / Zstd data compression */

  def detect_xz: Boolean =
    length >= 6 &&
      bytes(offset)     == 0xFD.toByte &&
      bytes(offset + 1) == 0x37.toByte &&
      bytes(offset + 2) == 0x7A.toByte &&
      bytes(offset + 3) == 0x58.toByte &&
      bytes(offset + 4) == 0x5A.toByte &&
      bytes(offset + 5) == 0x00.toByte

  def detect_zstd: Boolean =
    length >= 4 &&
      bytes(offset)     == 0x28.toByte &&
      bytes(offset + 1) == 0xB5.toByte &&
      bytes(offset + 2) == 0x2F.toByte &&
      bytes(offset + 3) == 0xFD.toByte

  def uncompress_xz(cache: Compress.Cache = Compress.Cache.none): Bytes =
    using(new xz.XZInputStream(stream(), cache.for_xz))(Bytes.read_stream(_, hint = length))

  def uncompress_zstd(cache: Compress.Cache = Compress.Cache.none): Bytes = {
    Zstd.init()
    val n = zstd.Zstd.decompressedSize(bytes, offset, length)
    if (n > 0 && n < Int.MaxValue) {
      Bytes(zstd.Zstd.decompress(array, n.toInt))
    }
    else {
      using(new zstd.ZstdInputStream(stream(), cache.for_zstd))(Bytes.read_stream(_, hint = length))
    }
  }

  def uncompress(cache: Compress.Cache = Compress.Cache.none): Bytes =
    if (detect_xz) uncompress_xz(cache = cache)
    else if (detect_zstd) uncompress_zstd(cache = cache)
    else error("Cannot detect compression scheme")

  def compress(
    options: Compress.Options = Compress.Options(),
    cache: Compress.Cache = Compress.Cache.none
  ): Bytes = {
    options match {
      case options_xz: Compress.Options_XZ =>
        val result = new ByteArrayOutputStream(length)
        using(new xz.XZOutputStream(result, options_xz.make, cache.for_xz))(write_stream)
        new Bytes(result.toByteArray, 0, result.size)
      case options_zstd: Compress.Options_Zstd =>
        Zstd.init()
        Bytes(zstd.Zstd.compress(if (offset == 0) bytes else array, options_zstd.level))
    }
  }

  def maybe_compress(
    options: Compress.Options = Compress.Options(),
    cache: Compress.Cache = Compress.Cache.none
  ) : (Boolean, Bytes) = {
    val compressed = compress(options = options, cache = cache)
    if (compressed.length < length) (true, compressed) else (false, this)
  }
}
