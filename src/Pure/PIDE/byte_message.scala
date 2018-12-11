/*  Title:      Pure/General/byte_message.scala
    Author:     Makarius

Byte-oriented messages.
*/

package isabelle

import java.io.{ByteArrayOutputStream, OutputStream, InputStream, IOException}


object Byte_Message
{
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


  /* hybrid messages: line or length+block (with content restriction) */

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
      stream.write(UTF8.bytes((msg.length + 1).toString))
      stream.write(10)
    }
    msg.write_stream(stream)
    stream.write(10)

    try { stream.flush() } catch { case _: IOException => }
  }

  def read_line_message(stream: InputStream): Option[Bytes] =
  {
    try {
      read_line(stream) match {
        case Some(line) =>
          if (is_length(line)) read_block(stream, Value.Int.parse(line.text)).map(_.trim_line)
          else Some(line)
        case None => None
      }
    }
    catch { case _: IOException => None }
  }
}
