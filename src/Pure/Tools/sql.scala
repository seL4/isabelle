/*  Title:      Pure/Tools/sql.scala
    Author:     Makarius

Support for SQL.
*/

package isabelle


object SQL
{
  /* concrete syntax */

  def quote_char(c: Char): String =
    c match {
      case '\u0000' => "\\0"
      case '\'' => "\\'"
      case '\"' => "\\\""
      case '\b' => "\\b"
      case '\n' => "\\n"
      case '\r' => "\\r"
      case '\t' => "\\t"
      case '\u001a' => "\\Z"
      case '\\' => "\\\\"
      case _ => c.toString
    }

  def quote_string(s: String): String =
    quote(s.map(quote_char(_)).mkString)

  def quote_ident(s: String): String = "`" + s + "`"
}
