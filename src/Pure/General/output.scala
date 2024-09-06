/*  Title:      Pure/General/output.scala
    Author:     Makarius

Console output channels.
*/

package isabelle


object Output {
  def writeln_text(msg: String): String = Protocol_Message.clean_output(msg)

  def warning_prefix(s: String): String = Library.prefix_lines("### ", s)
  def warning_text(msg: String): String = warning_prefix(Protocol_Message.clean_output(msg))

  def error_message_prefix(s: String): String = Library.prefix_lines("*** ", s)
  def error_message_text(msg: String): String =
    error_message_prefix(Protocol_Message.clean_output(msg))

  def output(s: String, stdout: Boolean = false, include_empty: Boolean = false): Unit =
    if (s.nonEmpty || include_empty) {
      if (stdout) Console.print(s + "\n") else Console.err.print(s + "\n")
    }

  def writeln(msg: String, stdout: Boolean = false, include_empty: Boolean = false): Unit =
    output(writeln_text(msg), stdout = stdout, include_empty = include_empty)

  def warning(msg: String, stdout: Boolean = false, include_empty: Boolean = false): Unit =
    output(warning_text(msg), stdout = stdout, include_empty = include_empty)

  def error_message(msg: String, stdout: Boolean = false, include_empty: Boolean = false): Unit =
    output(error_message_text(msg), stdout = stdout, include_empty = include_empty)
}
