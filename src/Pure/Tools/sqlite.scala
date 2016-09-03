/*  Title:      Pure/Tools/sqlite.scala
    Author:     Makarius
    Options:    :folding=explicit:

Support for SQLite databases.
*/

package isabelle


import java.sql.{Connection, DriverManager}


object SQLite
{
  /* database connection */

  def open_connection(path: Path): Connection =
  {
    val s0 = File.platform_path(path.expand)
    val s1 = if (Platform.is_windows) s0.replace('\\', '/') else s0
    DriverManager.getConnection("jdbc:sqlite:" + s1)
  }

  def with_connection[A](path: Path)(body: Connection => A): A =
  {
    val connection = open_connection(path)
    try { body(connection) } finally { connection.close }
  }


  /* SQL syntax */

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
