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
    val database = Path.explode("$ISABELLE_HOME_USER/servers.db")

    val name = SQL.Column.string("name", primary_key = true)
    val port = SQL.Column.int("port")
    val password = SQL.Column.string("password")
    val table = SQL.Table("isabelle_servers", List(name, port, password))

    sealed case class Entry(name: String, port: Int, password: String)
    {
      def print: String =
        "server " + quote(name) + " = 127.0.0.1:" + port + " (password " + quote(password) + ")"
    }
  }

  def list(): List[Data.Entry] =
    using(SQLite.open_database(Data.database))(list(_))

  def list(db: SQLite.Database): List[Data.Entry] =
    if (db.tables.contains(Data.table.name)) {
      db.using_statement(Data.table.select())(stmt =>
        stmt.execute_query().iterator(res =>
          Data.Entry(
            res.string(Data.name),
            res.int(Data.port),
            res.string(Data.password))).toList.sortBy(_.name))
    }
    else Nil

  def find(db: SQLite.Database, name: String): Option[Data.Entry] =
    list(db).find(entry => entry.name == name)

  def start(name: String = "", port: Int = 0, password: String = ""): (Data.Entry, Option[Thread]) =
  {
    using(SQLite.open_database(Data.database))(db =>
      db.transaction {
        find(db, name) match {
          case Some(entry) => (entry, None)
          case None =>
            val server = new Server(port, password)
            val entry = Data.Entry(name, server.port, server.password)

            Isabelle_System.bash("chmod 600 " + File.bash_path(Data.database)).check
            db.create_table(Data.table)
            db.using_statement(Data.table.insert())(stmt =>
            {
              stmt.string(1) = entry.name
              stmt.int(2) = entry.port
              stmt.string(3) = entry.password
              stmt.execute()
            })

            (entry, Some(server.thread))
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
            db.using_statement(Data.table.delete(Data.name.where_equal(name)))(_.execute)
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
      var operation_list = false
      var name = ""
      var port = 0

      val getopts =
        Getopts("""
Usage: isabelle server [OPTIONS]

  Options are:
    -L           list servers
    -n NAME      explicit server name
    -p PORT      explicit server port

  Manage resident Isabelle servers.
""",
          "L" -> (_ => operation_list = true),
          "n:" -> (arg => name = arg),
          "p:" -> (arg => port = Value.Int.parse(arg)))

      val more_args = getopts(args)
      if (more_args.nonEmpty) getopts.usage()

      if (operation_list) list().foreach(entry => Console.println(entry.print))
      else {
        val (entry, thread) = start(name, port)
        Console.println(entry.print)
        thread.foreach(_.join)
      }
    })
}

class Server private(_port: Int, _password: String)
{
  val socket = new ServerSocket(_port, 50, InetAddress.getByName("127.0.0.1"))
  def port: Int = socket.getLocalPort
  val password: String = proper_string(_password) getOrElse UUID.randomUUID().toString

  lazy val thread: Thread = Thread.currentThread // FIXME
}
