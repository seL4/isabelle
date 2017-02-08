/*  Title:      Pure/General/sql_database.scala
    Author:     Makarius

General SQL database support.
*/

package isabelle


import java.sql.{Connection, PreparedStatement}


trait SQL_Database
{
  /* connection */

  def connection: Connection

  def close() { connection.close }

  def transaction[A](body: => A): A =
  {
    val auto_commit = connection.getAutoCommit
    val savepoint = connection.setSavepoint

    try {
      connection.setAutoCommit(false)
      val result = body
      connection.commit
      result
    }
    catch { case exn: Throwable => connection.rollback(savepoint); throw exn }
    finally { connection.setAutoCommit(auto_commit) }
  }


  /* statements */

  def statement(sql: String): PreparedStatement = connection.prepareStatement(sql)

  def insert_statement(table: SQL.Table): PreparedStatement = statement(table.sql_insert)

  def select_statement(table: SQL.Table, columns: List[SQL.Column[Any]],
      sql: String = "", distinct: Boolean = false): PreparedStatement =
    statement(table.sql_select(columns, distinct) + (if (sql == "") "" else " " + sql))


  /* tables */

  def tables: List[String] =
    SQL.iterator(connection.getMetaData.getTables(null, null, "%", null))(_.getString(3)).toList

  def create_table(table: SQL.Table, strict: Boolean = true, rowid: Boolean = true): Unit =
    using(statement(table.sql_create(strict, rowid)))(_.execute())

  def drop_table(table: SQL.Table, strict: Boolean = true): Unit =
    using(statement(table.sql_drop(strict)))(_.execute())

  def create_index(table: SQL.Table, name: String, columns: List[SQL.Column[Any]],
      strict: Boolean = true, unique: Boolean = false): Unit =
    using(statement(table.sql_create_index(name, columns, strict, unique)))(_.execute())

  def drop_index(table: SQL.Table, name: String, strict: Boolean = true): Unit =
    using(statement(table.sql_drop_index(name, strict)))(_.execute())
}
