/*  Title:      Pure/Tools/server.scala
    Author:     Makarius

Resident Isabelle servers.
*/

package isabelle


import java.io.{BufferedReader, BufferedWriter, InputStreamReader, OutputStreamWriter,
  IOException}
import java.net.{Socket, ServerSocket, InetAddress}


object Server
{
  /* protocol */

  val commands: Map[String, PartialFunction[(Server, JSON.T), JSON.T]] =
    Map(
      "echo" -> { case (_, t) => t },
      "help" -> { case (_, JSON.empty) => commands.keySet.toList.sorted },
      "shutdown" -> { case (server, JSON.empty) => server.shutdown(); JSON.empty })

  object Reply extends Enumeration
  {
    val OK, ERROR = Value
  }


  /* socket connection */

  object Connection
  {
    def apply(socket: Socket): Connection =
      new Connection(socket)
  }

  class Connection private(socket: Socket)
  {
    override def toString: String = socket.toString

    def close() { socket.close }

    val reader = new BufferedReader(new InputStreamReader(socket.getInputStream, UTF8.charset))
    val writer = new BufferedWriter(new OutputStreamWriter(socket.getOutputStream, UTF8.charset))

    def read_line(): Option[String] =
      reader.readLine() match {
        case null => None
        case line => Some(line)
      }

    def write_line(msg: String)
    {
      require(split_lines(msg).length <= 1)
      writer.write(msg)
      writer.newLine()
      writer.flush()
    }

    def reply(r: Server.Reply.Value, t: JSON.T)
    {
      write_line(if (t == JSON.empty) r.toString else r.toString + " " + JSON.Format(t))
    }

    def reply_ok(t: JSON.T) { reply(Server.Reply.OK, t) }
    def reply_error(t: JSON.T) { reply(Server.Reply.ERROR, t) }
    def reply_error_message(message: String, more: (String, JSON.T)*): Unit =
      reply_error(Map("message" -> message) ++ more)
  }


  /* per-user servers */

  def print(port: Int, password: String): String =
    "127.0.0.1:" + port + " (password " + quote(password) + ")"

  object Data
  {
    val database = Path.explode("$ISABELLE_HOME_USER/servers.db")

    val name = SQL.Column.string("name").make_primary_key
    val port = SQL.Column.int("port")
    val password = SQL.Column.string("password")
    val table = SQL.Table("isabelle_servers", List(name, port, password))

    sealed case class Entry(name: String, port: Int, password: String)
    {
      override def toString: String =
        "server " + quote(name) + " = " + print(port, password)

      def connection(): Connection =
        Connection(new Socket(InetAddress.getByName("127.0.0.1"), port))

      def active(): Boolean =
        try { connection().close; true }
        catch { case _: IOException => false }
    }
  }

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
    list(db).find(entry => entry.name == name && entry.active)

  def start(name: String = "", port: Int = 0): (Data.Entry, Option[Server]) =
  {
    using(SQLite.open_database(Data.database))(db =>
      db.transaction {
        find(db, name) match {
          case Some(entry) => (entry, None)
          case None =>
            val server = new Server(port)
            val entry = Data.Entry(name, server.port, server.password)

            Isabelle_System.bash("chmod 600 " + File.bash_path(Data.database)).check
            db.create_table(Data.table)
            db.using_statement(Data.table.delete(Data.name.where_equal(name)))(_.execute)
            db.using_statement(Data.table.insert())(stmt =>
            {
              stmt.string(1) = entry.name
              stmt.int(2) = entry.port
              stmt.string(3) = entry.password
              stmt.execute()
            })

            (entry, Some(server))
        }
      })
  }

  def stop(name: String = ""): Boolean =
  {
    using(SQLite.open_database(Data.database))(db =>
      db.transaction {
        find(db, name) match {
          case Some(entry) =>
            using(entry.connection())(connection =>
              {
                connection.write_line(entry.password)
                connection.write_line("shutdown")
              })
            while(entry.active) { Thread.sleep(100) }
            true
          case None => false
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

      if (operation_list) {
        for (entry <- using(SQLite.open_database(Data.database))(list(_)) if entry.active)
          Output.writeln(entry.toString, stdout = true)
      }
      else {
        val (entry, server) = start(name, port)
        Output.writeln(entry.toString, stdout = true)
        server.foreach(_.join)
      }
    })
}

class Server private(_port: Int)
{
  server =>

  private val server_socket = new ServerSocket(_port, 50, InetAddress.getByName("127.0.0.1"))
  def port: Int = server_socket.getLocalPort
  val password: String = Library.UUID()

  override def toString: String = Server.print(port, password)

  private def handle(connection: Server.Connection)
  {
    connection.read_line() match {
      case None =>
      case Some(line) if line != password =>
        connection.reply_error("Bad password -- connection closed")
      case _ =>
        var finished = false
        while (!finished) {
          connection.read_line() match {
            case None => finished = true
            case Some(line) =>
              val cmd = line.takeWhile(c => Symbol.is_ascii_letter(c) || Symbol.is_ascii_letdig(c))
              val input = line.substring(cmd.length).dropWhile(Symbol.is_ascii_blank(_))
              Server.commands.get(cmd) match {
                case None => connection.reply_error("Bad command " + quote(cmd))
                case Some(body) =>
                  proper_string(input) getOrElse "{}" match {
                    case JSON.Format(arg) =>
                      if (body.isDefinedAt((server, arg))) {
                        try { connection.reply_ok(body(server, arg)) }
                        catch { case ERROR(msg) => connection.reply_error(msg) }
                      }
                      else {
                        connection.reply_error_message(
                          "Bad argument for command", "command" -> cmd, "argument" -> arg)
                      }
                    case _ =>
                      connection.reply_error_message(
                        "Malformed command-line", "command" -> cmd, "input" -> input)
                  }
              }
            case _ =>
          }
        }
    }
  }

  private lazy val server_thread: Thread =
    Standard_Thread.fork("server") {
      var finished = false
      while (!finished) {
        Exn.capture(server_socket.accept) match {
          case Exn.Res(socket) =>
            Standard_Thread.fork("server_connection")
              { using(Server.Connection(socket))(handle(_)) }
          case Exn.Exn(_) => finished = true
        }
      }
    }

  def join { server_thread.join; shutdown() }

  def shutdown() { server_socket.close }
}
