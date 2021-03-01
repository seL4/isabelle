/*  Title:      Pure/General/output.scala
    Author:     Makarius

Isabelle output channels.
*/

package isabelle


object Output
{
  def clean_yxml(msg: String): String =
    try { XML.content(Protocol_Message.clean_reports(YXML.parse_body(msg))) }
    catch { case ERROR(_) => msg }

  def writeln_text(msg: String): String = clean_yxml(msg)

  def warning_prefix(s: String): String = Library.prefix_lines("### ", s)
  def warning_text(msg: String): String = warning_prefix(clean_yxml(msg))

  def error_prefix(s: String): String = Library.prefix_lines("*** ", s)
  def error_message_text(msg: String): String = error_prefix(clean_yxml(msg))

  def writeln(msg: String, stdout: Boolean = false, include_empty: Boolean = false): Unit =
  {
    if (msg.nonEmpty || include_empty) {
      if (stdout) Console.print(writeln_text(msg) + "\n")
      else Console.err.print(writeln_text(msg) + "\n")
    }
  }

  def warning(msg: String, stdout: Boolean = false, include_empty: Boolean = false): Unit =
  {
    if (msg.nonEmpty || include_empty) {
      if (stdout) Console.print(warning_text(msg) + "\n")
      else Console.err.print(warning_text(msg) + "\n")
    }
  }

  def error_message(msg: String, stdout: Boolean = false, include_empty: Boolean = false): Unit =
  {
    if (msg.nonEmpty || include_empty) {
      if (stdout) Console.print(error_message_text(msg) + "\n")
      else Console.err.print(error_message_text(msg) + "\n")
    }
  }
}
