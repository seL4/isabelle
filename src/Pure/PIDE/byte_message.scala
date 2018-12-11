/*  Title:      Pure/General/byte_message.scala
    Author:     Makarius

Byte-oriented messages.
*/

package isabelle

import java.io.{ByteArrayOutputStream, OutputStream, InputStream, IOException}


object Byte_Message
{
  /* output operations */

  def write(stream: OutputStream, bytes: Bytes) { bytes.write_stream(stream) }

  def newline(stream: OutputStream) { stream.write(10) }

  def flush(stream: OutputStream): Unit =
    try { stream.flush() }
    catch { case _: IOException => }


  /* input operations */

  def read(stream: InputStream, length: Int): Bytes =
    Bytes.read_stream(stream, limit = length)

  def read_block(stream: InputStream, length: Int): Option[Bytes] =
  {
    val msg = read(stream, length)
    if (msg.length == length) Some(msg) else None
  }

  def read_line(stream: InputStream): Option[Bytes] =
  {
    val line = new ByteArrayOutputStream(100)
    var c = 0
    while ({ c = stream.read; c != -1 && c != 10 }) line.write(c)

    if (c == -1 && line.size == 0) None
    else {
      val a = line.toByteArray
      val n = a.length
      val len = if (n > 0 && a(n - 1) == 13) n - 1 else n
      Some(Bytes(a, 0, len))
    }
  }


  /* header with chunk lengths */

  private def err_header(line: String): Nothing =
    error("Malformed message header: " + quote(line))

  private def parse_header(line: String): List[Int] =
    try { space_explode(',', line).map(Value.Int.parse_nat) }
    catch { case ERROR(_) => err_header(line) }

  def read_header(stream: InputStream): Option[List[Int]] =
    read_line(stream).map(_.text).map(parse_header(_))

  def read_header1(stream: InputStream): Option[Int] =
    read_line(stream).map(_.text).map(line =>
      parse_header(line) match {
        case List(n) => n
        case _ => err_header(line)
      })

  def write_header(stream: OutputStream, ns: List[Int])
  {
    stream.write(UTF8.bytes(ns.mkString(",")))
    newline(stream)
  }


  /* messages with multiple chunks (arbitrary content) */

  def write_message(stream: OutputStream, chunks: List[Bytes])
  {
    write_header(stream, chunks.map(_.length))
    chunks.foreach(write(stream, _))
    flush(stream)
  }

  private def read_chunk(stream: InputStream, n: Int): Bytes =
  {
    val chunk = read(stream, n)
    val len = chunk.length
    if (len == n) chunk
    else error("Malformed message chunk: unexpected EOF after " + len + " of " + n + " bytes")
  }

  def read_message(stream: InputStream): Option[List[Bytes]] =
    read_header(stream).map(ns => ns.map(n => read_chunk(stream, n)))


  /* hybrid messages: line or length+block (restricted content) */

  private def is_length(msg: Bytes): Boolean =
    !msg.is_empty && msg.iterator.forall(b => Symbol.is_ascii_digit(b.toChar))

  private def has_line_terminator(msg: Bytes): Boolean =
  {
    val len = msg.length
    len > 0 && Symbol.is_ascii_line_terminator(msg.charAt(len - 1))
  }

  def write_line_message(stream: OutputStream, msg: Bytes)
  {
    if (is_length(msg) || has_line_terminator(msg))
      error ("Bad content for line message:\n" ++ msg.text.take(100))

    if (msg.length > 100 || msg.iterator.contains(10)) {
      write_header(stream, List(msg.length + 1))
    }
    write(stream, msg)
    newline(stream)
    flush(stream)
  }

  def read_line_message(stream: InputStream): Option[Bytes] =
    read_line(stream) match {
      case Some(line) =>
        if (is_length(line)) read_block(stream, Value.Int.parse(line.text)).map(_.trim_line)
        else Some(line)
      case None => None
    }
}
