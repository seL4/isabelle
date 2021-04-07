/*  Title:      Tools/VSCode/src/channel.scala
    Author:     Makarius

Channel with JSON RPC protocol.
*/

package isabelle.vscode


import isabelle._

import java.io.{InputStream, OutputStream, FileOutputStream, ByteArrayOutputStream, File => JFile}

import scala.collection.mutable


class Channel(in: InputStream, out: OutputStream, log: Logger = No_Logger, verbose: Boolean = false)
{
  /* read message */

  private val Content_Length = """^\s*Content-Length:\s*(\d+)\s*$""".r

  private def read_line(): String =
    Byte_Message.read_line(in) match {
      case Some(bytes) => bytes.text
      case None => ""
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
    val bytes = Bytes.read_stream(in, limit = n)
    if (bytes.length == n) bytes.text
    else error("Bad message content (unexpected EOF after " + bytes.length + " of " + n + " bytes)")
  }

  def read(): Option[JSON.T] =
  {
    read_header() match {
      case Nil => None
      case Content_Length(s) :: _ =>
        s match {
          case Value.Int(n) if n >= 0 =>
            val msg = read_content(n)
            val json = JSON.parse(msg)
            LSP.Message.log("IN: " + n, json, log, verbose)
            Some(json)
          case _ => error("Bad Content-Length: " + s)
        }
      case header => error(cat_lines("Malformed header:" :: header))
    }
  }


  /* write message */

  def write(json: JSON.T): Unit =
  {
    val msg = JSON.Format(json)
    val content = UTF8.bytes(msg)
    val n = content.length
    val header = UTF8.bytes("Content-Length: " + n + "\r\n\r\n")

    LSP.Message.log("OUT: " + n, json, log, verbose)
    out.synchronized {
      out.write(header)
      out.write(content)
      out.flush
    }
  }


  /* display message */

  def display_message(message_type: Int, msg: String, show: Boolean): Unit =
    write(LSP.DisplayMessage(message_type, Output.clean_yxml(msg), show))

  def error_message(msg: String): Unit = display_message(LSP.MessageType.Error, msg, true)
  def warning(msg: String): Unit = display_message(LSP.MessageType.Warning, msg, true)
  def writeln(msg: String): Unit = display_message(LSP.MessageType.Info, msg, true)

  def log_error_message(msg: String): Unit = display_message(LSP.MessageType.Error, msg, false)
  def log_warning(msg: String): Unit = display_message(LSP.MessageType.Warning, msg, false)
  def log_writeln(msg: String): Unit = display_message(LSP.MessageType.Info, msg, false)

  object Error_Logger extends Logger
  {
    def apply(msg: => String): Unit = log_error_message(msg)
  }


  /* progress */

  def progress(verbose: Boolean = false): Progress =
    new Progress {
      override def echo(msg: String): Unit = log_writeln(msg)
      override def echo_warning(msg: String): Unit = log_warning(msg)
      override def echo_error_message(msg: String): Unit = log_error_message(msg)
      override def theory(theory: Progress.Theory): Unit = if (verbose) echo(theory.message)
    }
}
