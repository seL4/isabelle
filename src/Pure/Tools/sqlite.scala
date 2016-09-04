/*  Title:      Pure/Tools/sqlite.scala
    Author:     Makarius

Support for SQLite databases.
*/

package isabelle


import java.sql.{Connection, DriverManager}


object SQLite
{
  /* database connection */

  class Database private [SQLite](path: Path, val connection: Connection)
  {
    override def toString: String = path.toString

    def close { connection.close }
  }

  def open_database(path: Path): Database =
  {
    val path0 = path.expand
    val s0 = File.platform_path(path0)
    val s1 = if (Platform.is_windows) s0.replace('\\', '/') else s0
    val connection = DriverManager.getConnection("jdbc:sqlite:" + s1)
    new Database(path0, connection)
  }

  def with_database[A](path: Path)(body: Database => A): A =
  {
    val db = open_database(path)
    try { body(db) } finally { db.close }
  }
}
