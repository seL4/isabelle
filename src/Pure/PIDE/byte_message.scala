/*  Title:      Pure/PIDE/byte_message.scala
    Author:     Makarius

Byte-oriented messages.
*/

package isabelle

import java.io.{OutputStream, InputStream, IOException}


object Byte_Message {
  /* output operations */

  def write(stream: OutputStream, bytes: List[Bytes]): Unit =
    bytes.foreach(_.write_stream(stream))

  def flush(stream: OutputStream): Unit =
    try { stream.flush() }
    catch { case _: IOException => }

  def write_line(stream: OutputStream, bytes: Bytes): Unit = {
    write(stream, List(bytes, Bytes.newline))
    flush(stream)
  }


  /* input operations */

  def read(stream: InputStream, n: Long): Bytes =
    Bytes.read_stream(stream, limit = n)

  def read_block(stream: InputStream, n: Long): (Option[Bytes], Long) = {
    val msg = read(stream, n)
    val len = msg.size
    (if (len == n) Some(msg) else None, len)
  }

  def read_line(stream: InputStream): Option[Bytes] = {
    var c = 0
    val line =
      Bytes.Builder.use(hint = 100) { builder =>
        while ({ c = stream.read; c != -1 && c != 10 }) {
          builder += c.toByte
        }
      }
    if (c == -1 && line.size == 0) None else Some(line.trim_line)
  }


  /* messages with multiple chunks (arbitrary content) */

  private def make_header(ns: List[Long]): List[Bytes] =
    List(Bytes(ns.mkString(",")), Bytes.newline)

  def write_message(stream: OutputStream, chunks: List[Bytes]): Unit = {
    write(stream, make_header(chunks.map(_.size)) ::: chunks)
    flush(stream)
  }

  private def parse_header(line: String): List[Long] = {
    val args = space_explode(',', line)
    if (args.forall(is_length)) args.map(Value.Long.parse)
    else error("Malformed message header: " + quote(line))
  }

  private def read_chunk(stream: InputStream, n: Long): Bytes =
    read_block(stream, n) match {
      case (Some(chunk), _) => chunk
      case (None, len) =>
        error("Malformed message chunk: unexpected EOF after " + len + " of " + n + " bytes")
    }

  def read_message(stream: InputStream): Option[List[Bytes]] =
    read_line(stream).map(line => parse_header(line.text).map(read_chunk(stream, _)))


  /* hybrid messages: line or length+block (restricted content) */

  private def is_length(str: String): Boolean =
    !str.isEmpty && str.iterator.forall(Symbol.is_ascii_digit) &&
      Value.Long.unapply(str).isDefined

  private def is_length(msg: Bytes): Boolean =
    !msg.is_empty && msg.byte_iterator.forall(b => Symbol.is_ascii_digit(b.toChar)) &&
      Value.Long.unapply(msg.text).isDefined

  def write_line_message(stream: OutputStream, msg: Bytes): Unit = {
    if (is_length(msg) || msg.terminated_line) {
      error ("Bad content for line message:\n" ++ msg.text.take(100))
    }

    val n = msg.size
    write(stream,
      (if (n > 100 || msg.byte_iterator.contains(10)) make_header(List(n + 1)) else Nil) :::
        List(msg, Bytes.newline))
    flush(stream)
  }

  def read_line_message(stream: InputStream): Option[Bytes] =
    read_line(stream) match {
      case Some(line) if is_length(line) =>
        val n = Value.Long.parse(line.text)
        read_block(stream, n)._1.map(_.trim_line)
      case res => res
    }
}
