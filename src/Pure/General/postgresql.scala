/*  Title:      Pure/General/postgresql.scala
    Author:     Makarius

Support for PostgreSQL databases.
*/

package isabelle


import java.sql.{DriverManager, Connection}


object PostgreSQL
{
  /** database connection **/

  val default_host = "localhost"
  val default_port = 5432

  def open_database(
    user: String,
    password: String,
    database: String = "",
    host: String = "",
    port: Int = default_port): Database =
  {
    require(user != "")

    val spec =
      (if (host != "") host else "localhost") +
      (if (port != default_port) ":" + port else "") + "/" +
      (if (database != "") database else user)
    val connection = DriverManager.getConnection("jdbc:postgresql://" + spec, user, password)
    new Database(spec, connection)
  }

  class Database private[PostgreSQL](spec: String, val connection: Connection)
  {
    override def toString: String = spec
  }
}
