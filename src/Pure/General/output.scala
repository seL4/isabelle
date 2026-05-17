/*  Title:      Pure/General/output.scala
    Author:     Makarius

Console output channels.
*/

package isabelle


object Output {
  /* kind */

  def warning_prefix(s: String): String = Library.prefix_lines("### ", s)
  def error_message_prefix(s: String): String = Library.prefix_lines("*** ", s)

  enum Kind { case writeln, warning, error_message }

  def make_text(kind: Kind, msg: String): String = {
    val text = Protocol_Message.clean_output(msg)
    kind match {
      case Kind.writeln => text
      case Kind.warning => warning_prefix(text)
      case Kind.error_message => error_message_prefix(text)
    }
  }

  def writeln_text(msg: String): String = make_text(Kind.writeln, msg)
  def warning_text(msg: String): String = make_text(Kind.warning, msg)
  def error_message_text(msg: String): String = make_text(Kind.error_message, msg)


  /* stream */

  def print_stream(s: String, stdout: Boolean = false): Unit = {
    val out = if (stdout) Console.out else Console.err
    out.print(s)
    out.flush()
  }

  def delete_lines(lines: Int, stdout: Boolean = false): Unit =
    if (lines > 0) print_stream("\u001b[" + lines + "F\u001b[J", stdout = stdout)


  /* output */

  def output(s: String, stdout: Boolean = false, include_empty: Boolean = false): Unit =
    if (s.nonEmpty || include_empty) print_stream(s + "\n", stdout = stdout)

  def writeln(msg: String, stdout: Boolean = false, include_empty: Boolean = false): Unit =
    output(writeln_text(msg), stdout = stdout, include_empty = include_empty)

  def warning(msg: String, stdout: Boolean = false, include_empty: Boolean = false): Unit =
    output(warning_text(msg), stdout = stdout, include_empty = include_empty)

  def error_message(msg: String, stdout: Boolean = false, include_empty: Boolean = false): Unit =
    output(error_message_text(msg), stdout = stdout, include_empty = include_empty)
}
