/*  Title:      Pure/General/sqlite.scala
    Author:     Makarius

Support for SQLite databases.
*/

package isabelle


import java.sql.{DriverManager, Connection}


object SQLite
{
  def open_database(path: Path): Database =
  {
    val path0 = path.expand
    val s0 = File.platform_path(path0)
    val s1 = if (Platform.is_windows) s0.replace('\\', '/') else s0
    val connection = DriverManager.getConnection("jdbc:sqlite:" + s1)
    new Database(path0, connection)
  }

  class Database private[SQLite](path: Path, val connection: Connection) extends SQL_Database
  {
    override def toString: String = path.toString

    def rebuild { using(statement("VACUUM"))(_.execute()) }
  }
}
