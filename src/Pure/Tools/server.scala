/*  Title:      Pure/Tools/server.scala
    Author:     Makarius

Resident Isabelle servers.
*/

package isabelle


import java.util.UUID
import java.net.{ServerSocket, InetAddress}


object Server
{
  /* per-user servers */

  object Data
  {
    val database = Path.explode("$ISABELLE_HOME_USER/server.db")

    val server_name = SQL.Column.string("server_name", primary_key = true)
    val server_port = SQL.Column.int("server_port")
    val password = SQL.Column.string("password")
    val table = SQL.Table("isabelle_servers", List(server_name, server_port, password))

    sealed case class Entry(server_name: String, server_port: Int, password: String)
    {
      def address: String = "127.0.0.1:" + server_port
    }
  }

  def list(): List[Data.Entry] =
    using(SQLite.open_database(Data.database))(list(_))

  def list(db: SQLite.Database): List[Data.Entry] =
    if (db.tables.contains(Data.table.name)) {
      db.using_statement(Data.table.select())(stmt =>
        stmt.execute_query().iterator(res =>
          Data.Entry(
            res.string(Data.server_name),
            res.int(Data.server_port),
            res.string(Data.password))).toList.sortBy(_.server_name))
    }
    else Nil

  def find(db: SQLite.Database, name: String): Option[Data.Entry] =
    list(db).find(entry => entry.server_name == name)

  def start(name: String = "", port: Int = 0): (Data.Entry, Boolean) =
  {
    using(SQLite.open_database(Data.database))(db =>
      db.transaction {
        find(db, name) match {
          case Some(entry) => (entry, false)
          case None =>
            val socket = new ServerSocket(port, 50, InetAddress.getByName("127.0.0.1"))
            val server = new Server(socket)
            val entry = Data.Entry(name, server.port, server.password)

            Isabelle_System.bash("chmod 600 " + File.bash_path(Data.database)).check
            db.create_table(Data.table)
            db.using_statement(Data.table.insert())(stmt =>
            {
              stmt.string(1) = entry.server_name
              stmt.int(2) = entry.server_port
              stmt.string(3) = entry.password
              stmt.execute()
            })
            (entry, true)
        }
      })
  }

  def stop(name: String = ""): Boolean =
  {
    using(SQLite.open_database(Data.database))(db =>
      db.transaction {
        find(db, name) match {
          case Some(entry) =>
            // FIXME shutdown server
            db.using_statement(Data.table.delete(Data.server_name.where_equal(name)))(_.execute)
            true
          case None =>
            false
        }
      })
  }


  /* Isabelle tool wrapper */

  val isabelle_tool =
    Isabelle_Tool("server", "manage resident Isabelle servers", args =>
    {
      var list_servers = false

      val getopts =
        Getopts("""
Usage: isabelle server [OPTIONS]

  Options are:
    -l           list servers

  Manage resident Isabelle servers.
""",
          "l" -> (_ => list_servers = true))

      val more_args = getopts(args)
      if (more_args.nonEmpty || !list_servers) getopts.usage()

      if (list_servers) list().foreach(entry =>
        Console.println("server " + quote(entry.server_name) + " = " + entry.address +
          " (password " + quote(entry.password) + ")"))
    })
}

class Server private(val socket: ServerSocket)
{
  def port: Int = socket.getLocalPort
  val password = UUID.randomUUID().toString
}
