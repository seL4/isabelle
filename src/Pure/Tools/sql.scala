/*  Title:      Pure/Tools/sql.scala
    Author:     Makarius

Generic support for SQL.
*/

package isabelle


import java.sql.ResultSet


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

  def quote_ident(s: String): String =
  {
    require(!s.contains('`'))
    "`" + s + "`"
  }


  /* columns */

  object Column
  {
    def int(name: String, strict: Boolean = true): Column[Int] = new Column_Int(name, strict)
    def long(name: String, strict: Boolean = true): Column[Long] = new Column_Long(name, strict)
    def double(name: String, strict: Boolean = true): Column[Double] = new Column_Double(name, strict)
    def string(name: String, strict: Boolean = true): Column[String] = new Column_String(name, strict)
    def bytes(name: String, strict: Boolean = true): Column[Bytes] = new Column_Bytes(name, strict)
  }

  abstract class Column[+A] private[SQL](val name: String, val strict: Boolean)
  {
    def sql_name: String = quote_ident(name)
    def sql_type: String
    def sql_decl: String = sql_name + " " + sql_type + (if (strict) " NOT NULL" else "")
    def string(rs: ResultSet): String =
    {
      val s = rs.getString(name)
      if (s == null) "" else s
    }
    def apply(rs: ResultSet): A
    def get(rs: ResultSet): Option[A] =
    {
      val x = apply(rs)
      if (rs.wasNull) None else Some(x)
    }

    override def toString: String = sql_decl
  }

  class Column_Int private[SQL](name: String, strict: Boolean)
    extends Column[Int](name, strict)
  {
    def sql_type: String = "INTEGER"
    def apply(rs: ResultSet): Int = rs.getInt(name)
  }

  class Column_Long private[SQL](name: String, strict: Boolean)
    extends Column[Long](name, strict)
  {
    def sql_type: String = "INTEGER"
    def apply(rs: ResultSet): Long = rs.getLong(name)
  }

  class Column_Double private[SQL](name: String, strict: Boolean)
    extends Column[Double](name, strict)
  {
    def sql_type: String = "REAL"
    def apply(rs: ResultSet): Double = rs.getDouble(name)
  }

  class Column_String private[SQL](name: String, strict: Boolean)
    extends Column[String](name, strict)
  {
    def sql_type: String = "TEXT"
    def apply(rs: ResultSet): String =
    {
      val s = rs.getString(name)
      if (s == null) "" else s
    }
  }

  class Column_Bytes private[SQL](name: String, strict: Boolean)
    extends Column[Bytes](name, strict)
  {
    def sql_type: String = "BLOB"
    def apply(rs: ResultSet): Bytes =
    {
      val bs = rs.getBytes(name)
      if (bs == null) Bytes.empty else Bytes(bs)
    }
  }


  /* tables */

  sealed case class Table(name: String, columns: Column[Any]*)
  {
    def sql_create(strict: Boolean, rowid: Boolean): String =
      "CREATE TABLE " + (if (strict) "" else " IF NOT EXISTS ") +
        quote_ident(name) + " " + columns.map(_.sql_decl).mkString("(", ", ", ")") +
        (if (rowid) "" else " WITHOUT ROWID")

    def sql_drop(strict: Boolean): String =
      "DROP TABLE " + (if (strict) "" else " IF EXISTS ") + quote_ident(name)
  }
}
