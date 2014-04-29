/*  Title:      Pure/General/output.ML
    Author:     Makarius

Isabelle output channels: plain text without markup.
*/

package isabelle


object Output
{
  def warning_text(msg: String): String = cat_lines(split_lines(msg).map("### " + _))
  def error_text(msg: String): String = cat_lines(split_lines(msg).map("*** " + _))

  def warning(msg: String) { System.err.println(warning_text(msg)) }
  def error_message(msg: String) { System.err.println(error_text(msg)) }
}

