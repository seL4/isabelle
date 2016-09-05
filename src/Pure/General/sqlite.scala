/*  Title:      Pure/General/sqlite.scala
    Author:     Makarius

Support for SQLite databases.
*/

package isabelle


import java.sql.{DriverManager, Connection, PreparedStatement}


object SQLite
{
  /** database connection **/

  def open_database(path: Path): Database =
  {
    val path0 = path.expand
    val s0 = File.platform_path(path0)
    val s1 = if (Platform.is_windows) s0.replace('\\', '/') else s0
    val connection = DriverManager.getConnection("jdbc:sqlite:" + s1)
    new Database(path0, connection)
  }

  class Database private [SQLite](path: Path, val connection: Connection)
  {
    override def toString: String = path.toString

    def close { connection.close }

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


    /* prepared statements */

    def statement(sql: String): PreparedStatement = connection.prepareStatement(sql)

    def insert_statement(table: SQL.Table): PreparedStatement = statement(table.sql_insert)


    /* tables */

    def tables: List[String] =
      SQL.iterator(connection.getMetaData.getTables(null, null, "%", null))(_.getString(3)).toList

    def create_table(table: SQL.Table, strict: Boolean = true, rowid: Boolean = true): Unit =
      using(statement(table.sql_create(strict, rowid)))(_.execute())

    def drop_table(table: SQL.Table, strict: Boolean = true): Unit =
      using(statement(table.sql_drop(strict)))(_.execute())
  }
}
