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

  def read(stream: InputStream, n: Int): Bytes =
    Bytes.read_stream(stream, limit = n)

  def read_block(stream: InputStream, n: Int): (Option[Bytes], Int) =
  {
    val msg = read(stream, n)
    val len = msg.length
    (if (len == n) Some(msg) else None, len)
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

  def write_header(stream: OutputStream, ns: List[Int])
  {
    stream.write(UTF8.bytes(ns.mkString(",")))
    newline(stream)
  }

  private def err_header(line: String): Nothing =
    error("Malformed message header: " + quote(line))

  private def parse_header(line: String): List[Int] =
    try { space_explode(',', line).map(Value.Nat.parse) }
    catch { case ERROR(_) => err_header(line) }

  def read_header(stream: InputStream): Option[List[Int]] =
    read_line(stream).map(_.text).map(parse_header(_))

  def read_header1(stream: InputStream): Option[Int] =
    read_line(stream).map(_.text).map(line =>
      parse_header(line) match {
        case List(n) => n
        case _ => err_header(line)
      })


  /* messages with multiple chunks (arbitrary content) */

  def write_message(stream: OutputStream, chunks: List[Bytes])
  {
    write_header(stream, chunks.map(_.length))
    chunks.foreach(write(stream, _))
    flush(stream)
  }

  private def read_chunk(stream: InputStream, n: Int): Bytes =
    read_block(stream, n) match {
      case (Some(chunk), _) => chunk
      case (None, len) =>
        error("Malformed message chunk: unexpected EOF after " + len + " of " + n + " bytes")
    }

  def read_message(stream: InputStream): Option[List[Bytes]] =
    read_header(stream).map(ns => ns.map(n => read_chunk(stream, n)))


  /* hybrid messages: line or length+block (restricted content) */

  private def is_length(msg: Bytes): Boolean =
    !msg.is_empty && msg.iterator.forall(b => Symbol.is_ascii_digit(b.toChar))

  private def is_terminated(msg: Bytes): Boolean =
  {
    val len = msg.length
    len > 0 && Symbol.is_ascii_line_terminator(msg.charAt(len - 1))
  }

  def write_line_message(stream: OutputStream, msg: Bytes)
  {
    if (is_length(msg) || is_terminated(msg))
      error ("Bad content for line message:\n" ++ msg.text.take(100))

    val n = msg.length
    if (n > 100 || msg.iterator.contains(10)) write_header(stream, List(n + 1))

    write(stream, msg)
    newline(stream)
    flush(stream)
  }

  def read_line_message(stream: InputStream): Option[Bytes] =
    read_line(stream) match {
      case None => None
      case Some(line) =>
        Value.Nat.unapply(line.text) match {
          case None => Some(line)
          case Some(n) => read_block(stream, n)._1.map(_.trim_line)
        }
    }
}
