/*  Title:      Pure/General/byte_message.scala
    Author:     Makarius

Byte-oriented messages.
*/

package isabelle

import java.io.{ByteArrayOutputStream, OutputStream, InputStream, IOException}


object Byte_Message
{
  /* output operations */

  def write(stream: OutputStream, bytes: List[Bytes]): Unit =
    bytes.foreach(_.write_stream(stream))

  def flush(stream: OutputStream): Unit =
    try { stream.flush() }
    catch { case _: IOException => }

  def write_line(stream: OutputStream, bytes: Bytes): Unit =
  {
    write(stream, List(bytes, Bytes.newline))
    flush(stream)
  }


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


  /* messages with multiple chunks (arbitrary content) */

  private def make_header(ns: List[Int]): List[Bytes] =
    List(Bytes(ns.mkString(",")), Bytes.newline)

  def write_message(stream: OutputStream, chunks: List[Bytes]): Unit =
  {
    write(stream, make_header(chunks.map(_.length)) ::: chunks)
    flush(stream)
  }

  private def parse_header(line: String): List[Int] =
    try { space_explode(',', line).map(Value.Nat.parse) }
    catch { case ERROR(_) => error("Malformed message header: " + quote(line)) }

  private def read_chunk(stream: InputStream, n: Int): Bytes =
    read_block(stream, n) match {
      case (Some(chunk), _) => chunk
      case (None, len) =>
        error("Malformed message chunk: unexpected EOF after " + len + " of " + n + " bytes")
    }

  def read_message(stream: InputStream): Option[List[Bytes]] =
    read_line(stream).map(line => parse_header(line.text).map(read_chunk(stream, _)))


  /* hybrid messages: line or length+block (restricted content) */

  private def is_length(msg: Bytes): Boolean =
    !msg.is_empty && msg.iterator.forall(b => Symbol.is_ascii_digit(b.toChar))

  private def is_terminated(msg: Bytes): Boolean =
  {
    val len = msg.length
    len > 0 && Symbol.is_ascii_line_terminator(msg.charAt(len - 1))
  }

  def write_line_message(stream: OutputStream, msg: Bytes): Unit =
  {
    if (is_length(msg) || is_terminated(msg))
      error ("Bad content for line message:\n" ++ msg.text.take(100))

    val n = msg.length
    write(stream,
      (if (n > 100 || msg.iterator.contains(10)) make_header(List(n + 1)) else Nil) :::
        List(msg, Bytes.newline))
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
