/*  Title:      Pure/General/bytes.scala
    Author:     Makarius

Scalable byte strings, with incremental construction (via Builder).
*/

package isabelle


import java.io.{ByteArrayInputStream, ByteArrayOutputStream, FileInputStream, FileOutputStream,
  InputStreamReader, InputStream, OutputStream, File => JFile}
import java.nio.ByteBuffer
import java.nio.charset.StandardCharsets.ISO_8859_1
import java.nio.channels.FileChannel
import java.nio.file.StandardOpenOption
import java.util.Arrays
import org.tukaani.xz
import com.github.luben.zstd

import scala.collection.mutable.ArrayBuffer
import scala.collection.mutable


object Bytes {
  /* internal sizes */

  private val array_size: Long = Int.MaxValue - 8  // see java.io.InputStream.MAX_BUFFER_SIZE
  private val string_size: Long = Int.MaxValue / 2
  private val block_size: Int = 16384  // see java.io.InputStream.DEFAULT_BUFFER_SIZE
  private val chunk_size: Long = Space.MiB(100).bytes

  class Too_Large(size: Long, limit: Long) extends IndexOutOfBoundsException {
    override def getMessage: String =
      "Bytes too large for particular operation: " +
        Space.bytes(size).print + " > " + Space.bytes(limit).print
  }


  /* main constructors */

  val empty: Bytes = new Bytes(None, new Array(0), 0L, 0L)

  def raw(s: String): Bytes =
    if (s.isEmpty) empty
    else Builder.use(hint = s.length) { builder => builder += s.getBytes(ISO_8859_1) }

  def apply(s: String): Bytes =
    if (s.isEmpty) empty
    else Builder.use(hint = s.length) { builder => builder += s }

  def apply(a: Array[Byte]): Bytes = apply(a, 0, a.length)

  def apply(a: Array[Byte], offset: Int, length: Int): Bytes =
    Builder.use(hint = length) { builder => builder += (a, offset, length) }

  val newline: Bytes = apply("\n")


  /* read */

  def read_stream(stream: InputStream, limit: Long = -1L, hint: Long = 0L): Bytes = {
    if (limit == 0) empty
    else {
      Builder.use(hint = if (limit > 0) limit else hint) { builder =>
        val buf_size = block_size
        val buf = new Array[Byte](block_size)
        var m = 0
        var n = 0L
        while ({
          val l = if (limit > 0) (limit - n).min(buf_size).toInt else buf_size
          m = stream.read(buf, 0, l)
          if (m > 0) {
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
          val buf_size = block_size
          val buf = ByteBuffer.allocate(buf_size)
          var m = 0
          var n = 0L
          while ({
            val l = (len - n).min(buf_size).toInt
            buf.limit(l)
            m = channel.read(buf)
            if (m > 0) {
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


  /* incremental builder: unsynchronized! */

  object Builder {
    def use(hint: Long = 0L)(body: Builder => Unit): Bytes = {
      val builder = new Builder(hint)
      body(builder)
      builder.done()
    }

    def use_stream(hint: Long = 0L)(body: OutputStream => Unit): Bytes = {
      val stream = new Stream(hint = hint)
      body(stream)
      stream.builder.done()
    }

    private class Stream(hint: Long = 0L) extends OutputStream {
      val builder = new Builder(hint)

      override def write(b: Int): Unit =
        { builder += b.toByte }

      override def write(array: Array[Byte], offset: Int, length: Int): Unit =
        { builder += (array, offset, length) }
    }
  }

  final class Builder private[Bytes](hint: Long) {
    builder =>

    private var chunks =
      new ArrayBuffer[Array[Byte]](if (hint <= 0) 16 else (hint / chunk_size).toInt)

    private var buffer_list: mutable.ListBuffer[Array[Byte]] = null
    private var buffer =
      new Array[Byte](if (hint <= 0) 1024 else (hint min chunk_size min array_size).toInt)
    private var buffer_index = 0
    private var buffer_total = 0

    private def buffer_content(): Array[Byte] =
      if (buffer_list != null) {
        val array = new Array[Byte](buffer_total)
        var i = 0
        for (b <- buffer_list) {
          val n = b.length
          System.arraycopy(b, 0, array, i, n)
          i += n
        }
        System.arraycopy(buffer, 0, array, i, buffer_index)
        array
      }
      else if (buffer_index == buffer.length) buffer else Arrays.copyOf(buffer, buffer_index)

    private def buffer_check(request: Int = 0): Unit =
      if (buffer_index == buffer.length) {
        if (buffer_total == chunk_size) {
          chunks += buffer_content()
          buffer_list = null
          buffer = new Array[Byte](chunk_size.toInt)
          buffer_total = 0
          buffer_index = 0
        }
        else {
          if (buffer_list == null) { buffer_list = new mutable.ListBuffer }
          buffer_list += buffer
          buffer_index = 0
          val limit = (chunk_size - buffer_total).toInt
          buffer = new Array[Byte]((buffer_total max request) min limit)
        }
      }

    def += (b: Byte): Unit = {
      buffer(buffer_index) = b
      buffer_total += 1
      buffer_index += 1
      buffer_check()
    }

    def += (array: Array[Byte], offset: Int, length: Int): Unit = {
      if (offset < 0 || length < 0 || offset.toLong + length.toLong > array.length) {
        throw new IndexOutOfBoundsException
      }
      else {
        var i = offset
        var n = length
        while (n > 0) {
          val l = n min (buffer.length - buffer_index)
          System.arraycopy(array, i, buffer, buffer_index, l)
          buffer_total += l
          buffer_index += l
          i += l
          n -= l
          buffer_check(request = n)
        }
      }
    }

    def += (s: String): Unit =
      if (s.length > 0) { builder += UTF8.bytes(s) }

    def += (array: Array[Byte]): Unit = { builder += (array, 0, array.length) }

    def += (a: Subarray): Unit = { builder += (a.array, a.offset, a.length) }

    private def done(): Bytes = {
      val cs = chunks.toArray
      val b = buffer_content()
      val size = cs.foldLeft(b.length.toLong)({ case (n, a) => n + a.length })
      chunks = null
      buffer_list = null
      buffer = null
      if (size == 0) empty
      else new Bytes(if (cs.isEmpty) None else Some(cs), b, 0L, size)
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
) extends YXML.Source {
  bytes =>

  assert(
    (chunks.isEmpty ||
      chunks.get.nonEmpty &&
      chunks.get.forall(chunk => chunk.length == Bytes.chunk_size)) &&
    chunk0.length < Bytes.chunk_size)

  override def is_empty: Boolean = size == 0

  def proper: Option[Bytes] = if (is_empty) None else Some(bytes)

  def is_sliced: Boolean =
    offset != 0L || {
      chunks match {
        case None => size != chunk0.length
        case Some(cs) =>
          val physical_size = cs.foldLeft(chunk0.length.toLong)((n, c) => n + c.length)
          size != physical_size
      }
    }

  override def toString: String =
    if (is_empty) "Bytes.empty"
    else "Bytes(" + Space.bytes(size).print + if_proper(is_sliced, ", sliced") + ")"


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

  // signed byte
  def byte(i: Long): Byte =
    if (0 <= i && i < size) byte_unchecked(i)
    else throw new IndexOutOfBoundsException

  // unsigned char
  def char(i: Long): Char = (byte(i).toInt & 0xff).toChar

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
    else bytes

  def terminated_line: Boolean =
    size >= 1 && (byte_unchecked(size - 1) == 13 || byte_unchecked(size - 1) == 10)

  def trim_line: Bytes =
    if (size >= 2 && byte_unchecked(size - 2) == 13 && byte_unchecked(size - 1) == 10) {
      slice(0, size - 2)
    }
    else if (size >= 1 && (byte_unchecked(size - 1) == 13 || byte_unchecked(size - 1) == 10)) {
      slice(0, size - 1)
    }
    else bytes


  /* separated chunks */

  def separated_chunks(sep: Byte): Iterator[Bytes] =
    new Iterator[Bytes] {
      private var start: Long = -1
      private var stop: Long = -1

      private def end(i: Long): Long = {
        var j = i
        while (j < bytes.size && byte_unchecked(j) != sep) { j += 1 }
        j
      }

      // init
      if (!bytes.is_empty) { start = 0; stop = end(0) }

      def hasNext: Boolean =
        0 <= start && start <= stop && stop <= bytes.size

      def next(): Bytes =
        if (hasNext) {
          val chunk = bytes.slice(start, stop)
          if (stop < bytes.size) { start = stop + 1; stop = end(start) }
          else { start = -1; stop = -1 }
          chunk
        }
        else throw new NoSuchElementException
    }

  def space_explode(sep: Byte): List[Bytes] = separated_chunks(sep).toList

  def split_lines: List[Bytes] = space_explode(10)

  // YXML.Source operations
  override def is_X: Boolean = size == 1 && byte_unchecked(0) == YXML.X_byte
  override def is_Y: Boolean = size == 1 && byte_unchecked(0) == YXML.Y_byte
  override def iterator_X: Iterator[Bytes] = separated_chunks(YXML.X_byte)
  override def iterator_Y: Iterator[Bytes] = separated_chunks(YXML.Y_byte)


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
        if (bytes.eq(other)) true
        else if (size != other.size) false
        else {
          if (chunks.isEmpty && other.chunks.isEmpty) {
            Arrays.equals(chunk0, offset.toInt, (offset + size).toInt,
              other.chunk0, other.offset.toInt, (other.offset + other.size).toInt)
          }
          else if (!is_sliced && !other.is_sliced) {
            (subarray_iterator zip other.subarray_iterator)
              .forall((a, b) => Arrays.equals(a.array, b.array))
          }
          else sha1_digest == other.sha1_digest
        }
      case _ => false
    }
  }


  /* content */

  def + (other: Bytes): Bytes =
    if (other.is_empty) bytes
    else if (is_empty) other
    else {
      Bytes.Builder.use(hint = size + other.size) { builder =>
        for (a <- subarray_iterator ++ other.subarray_iterator) {
          builder += a
        }
      }
    }

  def make_array: Array[Byte] = {
    val n =
      if (size <= Bytes.array_size) size.toInt
      else throw new Bytes.Too_Large(size, Bytes.array_size)
    val buf = new ByteArrayOutputStream(n)
    for (a <- subarray_iterator) { buf.write(a.array, a.offset, a.length) }
    buf.toByteArray
  }

  def text: String =
    if (is_empty) ""
    else {
      val reader = new InputStreamReader(stream(), UTF8.charset)
      val buf = new Array[Char]((size min Bytes.string_size).toInt + 1)
      var m = 0
      var n = 0
      while (m >= 0 && n < buf.length) {
        m = reader.read(buf, n, (buf.length - n) min Bytes.block_size)
        if (m > 0) { n += m }
      }
      require(m == -1, "Malformed UTF-8 string: overlong result")
      new String(buf, 0, n)
    }

  def wellformed_text: Option[String] =
    try {
      val s = text
      if (bytes == Bytes(s)) Some(s) else None
    }
    catch { case ERROR(_) => None }


  /* Base64 data representation */

  def encode_base64: Bytes =
    Bytes.Builder.use_stream(hint = (size * 1.5).round) { out =>
      using(Base64.encode_stream(out))(write_stream(_))
    }

  def decode_base64: Bytes =
    using(Base64.decode_stream(stream()))(Bytes.read_stream(_, hint = (size / 1.2).round))

  def maybe_encode_base64: (Boolean, String) =
    wellformed_text match {
      case Some(s) => (false, s)
      case None => (true, encode_base64.text)
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

        override def read(buffer: Array[Byte], start: Int, length: Int): Int = {
          if (length < 16) super.read(buffer, start, length)
          else {
            val index0 = index
            index = (index + length) min size
            val n = (index - index0).toInt
            if (n == 0) -1
            else {
              var i = start
              for (a <- slice(index0, index).subarray_iterator) {
                val l = a.length
                if (l > 0) {
                  System.arraycopy(a.array, a.offset, buffer, i, l)
                  i += l
                }
              }
              n
            }
          }
        }
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
    using(new zstd.ZstdInputStream(stream(), cache.for_zstd))(Bytes.read_stream(_, hint = size))
  }

  def uncompress(cache: Compress.Cache = Compress.Cache.none): Bytes =
    if (detect_xz) uncompress_xz(cache = cache)
    else if (detect_zstd) uncompress_zstd(cache = cache)
    else error("Cannot detect compression scheme")

  def compress(
    options: Compress.Options = Compress.Options(),
    cache: Compress.Cache = Compress.Cache.none
  ): Bytes = {
    Bytes.Builder.use_stream(hint = size) { out =>
      using(
        options match {
          case options_xz: Compress.Options_XZ =>
            new xz.XZOutputStream(out, options_xz.make, cache.for_xz)
          case options_zstd: Compress.Options_Zstd =>
            new zstd.ZstdOutputStream(out, cache.for_zstd, options_zstd.level)
        }
      ) { s => for (a <- subarray_iterator) s.write(a.array, a.offset, a.length) }
    }
  }

  def maybe_compress(
    options: Compress.Options = Compress.Options(),
    cache: Compress.Cache = Compress.Cache.none
  ) : (Boolean, Bytes) = {
    val compressed = compress(options = options, cache = cache)
    if (compressed.size < size) (true, compressed) else (false, bytes)
  }
}
