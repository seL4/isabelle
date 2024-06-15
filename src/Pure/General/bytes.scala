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

import scala.collection.mutable.ArrayBuffer


object Bytes {
  /* internal sizes */

  val array_size: Long = Int.MaxValue - 8  // see java.io.InputStream.MAX_BUFFER_SIZE
  val chunk_size: Long = Space.MiB(100).bytes
  val block_size: Int = 8192

  class Too_Large(size: Long) extends IndexOutOfBoundsException {
    override def getMessage: String =
      "Bytes too large for particular operation: " +
        Space.bytes(size).print + " > " + Space.bytes(array_size).print
  }


  /* main constructors */

  private def reuse_array(bytes: Array[Byte]): Bytes =
    if (bytes.length <= chunk_size) new Bytes(None, bytes, 0L, bytes.length.toLong)
    else apply(bytes)

  val empty: Bytes = reuse_array(new Array(0))

  def apply(s: CharSequence): Bytes = {
    val str = s.toString
    if (str.isEmpty) empty
    else Builder.use(hint = str.length) { builder => builder += str }
  }

  def apply(a: Array[Byte]): Bytes = apply(a, 0, a.length)

  def apply(a: Array[Byte], offset: Int, length: Int): Bytes =
    Builder.use(hint = length) { builder => builder += (a, offset, length) }

  val newline: Bytes = apply("\n")

  def decode_base64(s: String): Bytes = Bytes.reuse_array(Base64.decode(s))


  /* read */

  def read_stream(stream: InputStream, limit: Long = -1L, hint: Long = 0L): Bytes = {
    if (limit == 0) empty
    else {
      Builder.use(hint = if (limit > 0) limit else hint) { builder =>
        val buf = new Array[Byte](Bytes.block_size)
        var m = 0
        var n = 0L
        while ({
          val l = if (limit > 0) ((limit - n) min buf.length).toInt else buf.length
          m = stream.read(buf, 0, l)
          if (m != -1) {
            builder += (buf, 0, m)
            n += m
          }
          m != -1 && (limit < 0 || limit > n)
        }) ()
      }
    }
  }

  def read_url(name: String): Bytes = using(Url(name).open_stream())(read_stream(_))

  def read_file(path: Path, offset: Long = 0L, limit: Long = -1L): Bytes = {
    val length = File.size(path)
    val start = offset.max(0L)
    val len = (length - start).max(0L).min(if (limit < 0) Long.MaxValue else limit)
    if (len == 0L) empty
    else {
      Builder.use(hint = len) { builder =>
        using(FileChannel.open(path.java_path, StandardOpenOption.READ)) { channel =>
          channel.position(start)
          val buf = ByteBuffer.allocate(Bytes.block_size)
          var m = 0
          var n = 0L
          while ({
            m = channel.read(buf)
            if (m != -1) {
              builder += (buf.array(), 0, m)
              buf.clear()
              n += m
            }
            m != -1 && len > n
          }) ()
        }
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


  /* incremental builder: synchronized */

  private def make_size(chunks: Array[Array[Byte]], buffer: Array[Byte]): Long =
    chunks.foldLeft(buffer.length.toLong)((n, chunk) => n + chunk.length)

  object Builder {
    def use(hint: Long = 0L)(body: Builder => Unit): Bytes = {
      val chunks_size = if (hint <= 0) 16 else (hint / chunk_size).toInt
      val buffer_size = if (hint <= 0) 1024 else (hint min chunk_size min array_size).toInt
      val builder = new Builder(chunks_size, buffer_size)
      body(builder)
      builder.done()
    }
  }

  final class Builder private[Bytes](chunks_size: Int, buffer_size: Int) {
    private var chunks = new ArrayBuffer[Array[Byte]](chunks_size)
    private var buffer = new ByteArrayOutputStream(buffer_size)

    private def buffer_free(): Int = chunk_size.toInt - buffer.size()
    private def buffer_check(): Unit =
      if (buffer_free() == 0) {
        chunks += buffer.toByteArray
        buffer = new ByteArrayOutputStream
      }

    def += (array: Array[Byte], offset: Int, length: Int): Unit = {
      if (offset < 0 || length < 0 || offset.toLong + length.toLong > array.length) {
        throw new IndexOutOfBoundsException
      }
      else if (length > 0) {
        synchronized {
          var i = offset
          var n = length
          while (n > 0) {
            val m = buffer_free()
            if (m > 0) {
              val l = m min n
              buffer.write(array, i, l)
              i += l
              n -= l
            }
            buffer_check()
          }
        }
      }
    }

    def += (array: Array[Byte]): Unit = { this += (array, 0, array.length) }

    def += (a: Subarray): Unit = { this += (a.array, a.offset, a.length) }

    def += (string: String): Unit = if (string.nonEmpty) { this += UTF8.bytes(string) }

    private def done(): Bytes = synchronized {
      val cs = chunks.toArray
      val b = buffer.toByteArray
      chunks = null
      buffer = null
      new Bytes(if (cs.isEmpty) None else Some(cs), b, 0L, make_size(cs, b))
    }
  }


  /* subarray */

  object Subarray {
    val empty: Subarray = new Subarray(new Array[Byte](0), 0, 0)

    def apply(array: Array[Byte], offset: Int, length: Int): Subarray = {
      val n = array.length
      if (0 <= offset && offset < n && 0 <= length && offset + length <= n) {
        if (length == 0) empty
        else new Subarray(array, offset, length)
      }
      else throw new IndexOutOfBoundsException
    }
  }

  final class Subarray private(
    val array: Array[Byte],
    val offset: Int,
    val length: Int
  ) {
    override def toString: String = "Bytes.Subarray(" + Space.bytes(length).print + ")"

    def byte_iterator: Iterator[Byte] =
      if (length == 0) Iterator.empty
      else { for (i <- (offset until (offset + length)).iterator) yield array(i) }
  }
}

final class Bytes private(
  protected val chunks: Option[Array[Array[Byte]]],
  protected val chunk0: Array[Byte],
  protected val offset: Long,
  val size: Long
) extends Bytes.Vec {
  assert(
    (chunks.isEmpty ||
      chunks.get.nonEmpty &&
      chunks.get.forall(chunk => chunk.length == Bytes.chunk_size)) &&
    chunk0.length < Bytes.chunk_size)

  def is_empty: Boolean = size == 0

  def is_sliced: Boolean =
    offset != 0L || {
      chunks match {
        case None => size != chunk0.length
        case Some(cs) => size != Bytes.make_size(cs, chunk0)
      }
    }

  override def toString: String =
    if (is_empty) "Bytes.empty"
    else "Bytes(" + Space.bytes(size).print + if_proper(is_sliced, ", sliced") + ")"

  def small_size: Int =
    if (size > Bytes.array_size) throw new Bytes.Too_Large(size)
    else size.toInt


  /* slice */

  def slice(i: Long, j: Long): Bytes =
    if (0 <= i && i <= j && j <= size) {
      if (i == j) Bytes.empty
      else new Bytes(chunks, chunk0, offset + i, j - i)
    }
    else throw new IndexOutOfBoundsException

  def unslice: Bytes =
    if (is_sliced) {
      Bytes.Builder.use(hint = size) { builder =>
        for (a <- subarray_iterator) { builder += a }
      }
    }
    else this

  def trim_line: Bytes =
    if (size >= 2 && byte_unchecked(size - 2) == 13 && byte_unchecked(size - 1) == 10) {
      slice(0, size - 2)
    }
    else if (size >= 1 && (byte_unchecked(size - 1) == 13 || byte_unchecked(size - 1) == 10)) {
      slice(0, size - 1)
    }
    else this


  /* elements: signed Byte or unsigned Char */

  protected def byte_unchecked(i: Long): Byte = {
    val a = offset + i
    chunks match {
      case None => chunk0(a.toInt)
      case Some(cs) =>
        val b = a % Bytes.chunk_size
        val c = a / Bytes.chunk_size
        if (c < cs.length) cs(c.toInt)(b.toInt) else chunk0(b.toInt)
    }
  }

  def byte(i: Long): Byte =
    if (0 <= i && i < size) byte_unchecked(i)
    else throw new IndexOutOfBoundsException

  def apply(i: Long): Char = (byte(i).toInt & 0xff).toChar

  protected def subarray_iterator: Iterator[Bytes.Subarray] =
    if (is_empty) Iterator.empty
    else if (chunks.isEmpty) Iterator(Bytes.Subarray(chunk0, offset.toInt, size.toInt))
    else {
      val end_offset = offset + size
      for ((array, index) <- (chunks.get.iterator ++ Iterator(chunk0)).zipWithIndex) yield {
        val array_start = Bytes.chunk_size * index
        val array_stop = array_start + array.length
        if (offset < array_stop && array_start < end_offset) {
          val i = (array_start max offset) - array_start
          val j = (array_stop min end_offset) - array_start
          Bytes.Subarray(array, i.toInt, (j - i).toInt)
        }
        else Bytes.Subarray.empty
      }
    }

  def byte_iterator: Iterator[Byte] =
    for {
      a <- subarray_iterator
      b <- a.byte_iterator
    } yield b


  /* hash and equality */

  lazy val sha1_digest: SHA1.Digest =
    if (is_empty) SHA1.digest_empty
    else {
      SHA1.make_digest { sha =>
        for (a <- subarray_iterator if a.length > 0) {
          sha.update(a.array, a.offset, a.length)
        }
      }
    }

  override def hashCode(): Int = sha1_digest.hashCode()

  override def equals(that: Any): Boolean = {
    that match {
      case other: Bytes =>
        if (this.eq(other)) true
        else if (size != other.size) false
        else if (chunks.isEmpty && size <= 10 * SHA1.digest_length) {
          Arrays.equals(chunk0, offset.toInt, (offset + size).toInt,
            other.chunk0, other.offset.toInt, (other.offset + other.size).toInt)
        }
        else sha1_digest == other.sha1_digest
      case _ => false
    }
  }


  /* content */

  def make_array: Array[Byte] = {
    val buf = new ByteArrayOutputStream(small_size)
    for (a <- subarray_iterator) { buf.write(a.array, a.offset, a.length) }
    buf.toByteArray
  }

  def text: String =
    if (is_empty) ""
    else if (byte_iterator.forall(_ >= 0)) {
      new String(make_array, UTF8.charset)
    }
    else UTF8.decode_permissive_bytes(this)

  def wellformed_text: Option[String] =
    try {
      val s = text
      if (this == Bytes(s)) Some(s) else None
    }
    catch { case ERROR(_) => None }

  def encode_base64: String = Base64.encode(make_array)

  def maybe_encode_base64: (Boolean, String) =
    wellformed_text match {
      case Some(s) => (false, s)
      case None => (true, encode_base64)
    }

  def proper: Option[Bytes] = if (is_empty) None else Some(this)
  def proper_text: Option[String] = if (is_empty) None else Some(text)

  def +(other: Bytes): Bytes =
    if (other.is_empty) this
    else if (is_empty) other
    else {
      Bytes.Builder.use(hint = size + other.size) { builder =>
        for (a <- subarray_iterator ++ other.subarray_iterator) {
          builder += a
        }
      }
    }


  /* streams */

  def stream(): InputStream =
    if (chunks.isEmpty) new ByteArrayInputStream(chunk0, offset.toInt, size.toInt)
    else {
      new InputStream {
        private var index = 0L

        def read(): Int = {
          if (index < size) {
            val res = byte_unchecked(index).toInt & 0xff
            index += 1
            res
          }
          else -1
        }

        override def readAllBytes(): Array[Byte] = make_array
      }
    }

  def write_stream(stream: OutputStream): Unit =
    for (a <- subarray_iterator if a.length > 0) {
      stream.write(a.array, a.offset, a.length)
    }


  /* XZ / Zstd data compression */

  def detect_xz: Boolean =
    size >= 6 &&
      byte_unchecked(0) == 0xFD.toByte &&
      byte_unchecked(1) == 0x37.toByte &&
      byte_unchecked(2) == 0x7A.toByte &&
      byte_unchecked(3) == 0x58.toByte &&
      byte_unchecked(4) == 0x5A.toByte &&
      byte_unchecked(5) == 0x00.toByte

  def detect_zstd: Boolean =
    size >= 4 &&
      byte_unchecked(0) == 0x28.toByte &&
      byte_unchecked(1) == 0xB5.toByte &&
      byte_unchecked(2) == 0x2F.toByte &&
      byte_unchecked(3) == 0xFD.toByte

  def uncompress_xz(cache: Compress.Cache = Compress.Cache.none): Bytes =
    using(new xz.XZInputStream(stream(), cache.for_xz))(Bytes.read_stream(_, hint = size))

  def uncompress_zstd(cache: Compress.Cache = Compress.Cache.none): Bytes = {
    Zstd.init()

    def uncompress_stream(hint: Long): Bytes =
      using(new zstd.ZstdInputStream(stream(), cache.for_zstd)) { inp =>
        Bytes.read_stream(inp, hint = hint)
      }

    if (chunks.isEmpty) {
      zstd.Zstd.decompressedSize(chunk0, offset.toInt, size.toInt) match {
        case 0 => Bytes.empty
        case n if n <= Bytes.array_size && !is_sliced =>
          Bytes.reuse_array(zstd.Zstd.decompress(chunk0, n.toInt))
        case n => uncompress_stream(n)
      }
    }
    else uncompress_stream(size / 2)
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
        val out = new ByteArrayOutputStream((size min Bytes.array_size).toInt)
        using(new xz.XZOutputStream(out, options_xz.make, cache.for_xz))(write_stream)
        Bytes(out.toByteArray)
      case options_zstd: Compress.Options_Zstd =>
        Zstd.init()
        val inp = if (chunks.isEmpty && !is_sliced) chunk0 else make_array
        Bytes(zstd.Zstd.compress(inp, options_zstd.level))
    }
  }

  def maybe_compress(
    options: Compress.Options = Compress.Options(),
    cache: Compress.Cache = Compress.Cache.none
  ) : (Boolean, Bytes) = {
    val compressed = compress(options = options, cache = cache)
    if (compressed.size < size) (true, compressed) else (false, this)
  }
}
