/*  Title:      Tools/VSCode/src/channel.scala
    Author:     Makarius

Channel with JSON RPC protocol.
*/

package isabelle.vscode


import isabelle._

import java.io.{InputStream, OutputStream, FileOutputStream, ByteArrayOutputStream, File => JFile}

import scala.collection.mutable


class Channel(in: InputStream, out: OutputStream, log: Logger = No_Logger)
{
  /* read message */

  private val Content_Length = """^\s*Content-Length:\s*(\d+)\s*$""".r

  private def read_line(): String =
  {
    val buffer = new ByteArrayOutputStream(100)
    var c = 0
    while ({ c = in.read; c != -1 && c != 10 }) buffer.write(c)
    Library.trim_line(buffer.toString(UTF8.charset_name))
  }

  private def read_header(): List[String] =
  {
    val header = new mutable.ListBuffer[String]
    var line = ""
    while ({ line = read_line(); line != "" }) header += line
    header.toList
  }

  private def read_content(n: Int): String =
  {
    val buffer = new Array[Byte](n)
    var i = 0
    var m = 0
    do {
      m = in.read(buffer, i, n - i)
      if (m != -1) i += m
    }
    while (m != -1 && n > i)

    if (i == n) new String(buffer, UTF8.charset)
    else error("Bad message content (unexpected EOF after " + i + " of " + n + " bytes)")
  }

  def read(): Option[JSON.T] =
  {
    read_header() match {
      case Nil => None
      case Content_Length(s) :: _ =>
        s match {
          case Value.Int(n) if n >= 0 =>
            val msg = read_content(n)
            log("IN:\n" + msg)
            Some(JSON.parse(msg))
          case _ => error("Bad Content-Length: " + s)
        }
      case header => error(cat_lines("Malformed header:" :: header))
    }
  }


  /* write message */

  def write(json: JSON.T)
  {
    val msg = JSON.Format(json)
    log("OUT:\n" + msg)

    val content = UTF8.bytes(msg)
    val header = UTF8.bytes("Content-Length: " + content.length + "\r\n\r\n")
    out.synchronized {
      out.write(header)
      out.write(content)
      out.flush
    }
  }


  /* display message */

  def display_message(message_type: Int, msg: String, show: Boolean = true): Unit =
    write(Protocol.DisplayMessage(message_type, Output.clean_yxml(msg), show))

  def error_message(msg: String) { display_message(Protocol.MessageType.Error, msg, true) }
  def warning(msg: String) { display_message(Protocol.MessageType.Warning, msg, true) }
  def writeln(msg: String) { display_message(Protocol.MessageType.Info, msg, true) }

  def log_error_message(msg: String) { display_message(Protocol.MessageType.Error, msg, false) }
  def log_warning(msg: String) { display_message(Protocol.MessageType.Warning, msg, false) }
  def log_writeln(msg: String) { display_message(Protocol.MessageType.Info, msg, false) }

  object Error_Logger extends Logger
  {
    def apply(msg: => String) { log_error_message(msg) }
  }


  /* progress */

  def make_progress(verbose: Boolean = false): Progress =
    new Progress {
      override def echo(msg: String): Unit = log_writeln(msg)
      override def theory(session: String, theory: String): Unit =
        if (verbose) echo(session + ": theory " + theory)
    }
}
