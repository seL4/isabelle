/*  Title:      Pure/Tools/server.scala
    Author:     Makarius

Resident Isabelle servers.
*/

package isabelle


import java.io.{BufferedInputStream, BufferedOutputStream, BufferedReader, BufferedWriter,
  InputStreamReader, OutputStreamWriter, IOException}
import java.net.{Socket, SocketException, SocketTimeoutException, ServerSocket, InetAddress}


object Server
{
  /* protocol */

  def split_line(line: String): (String, String) =
  {
    val head = line.takeWhile(c => Symbol.is_ascii_letter(c) || Symbol.is_ascii_letdig(c))
    val rest = line.substring(head.length).dropWhile(Symbol.is_ascii_blank(_))
    (head, proper_string(rest) getOrElse "{}")
  }

  val commands: Map[String, PartialFunction[(Server, JSON.T), JSON.T]] =
    Map(
      "echo" -> { case (_, t) => t },
      "help" -> { case (_, JSON.empty) => commands.keySet.toList.sorted },
      "shutdown" -> { case (server, JSON.empty) => server.close(); JSON.empty })

  object Reply extends Enumeration
  {
    val OK, ERROR, NOTE = Value

    def unapply(line: String): Option[(Reply.Value, JSON.T)] =
    {
      if (line == "") None
      else {
        val (reply, output) = split_line(line)
        try { Some((withName(reply), JSON.parse(output, strict = false))) }
        catch {
          case _: NoSuchElementException => None
          case Exn.ERROR(_) => None
        }
      }
    }
  }


  /* socket connection */

  object Connection
  {
    def apply(socket: Socket): Connection =
      new Connection(socket)
  }

  class Connection private(val socket: Socket)
  {
    override def toString: String = socket.toString

    def close() { socket.close }

    val in = new BufferedInputStream(socket.getInputStream)
    val out = new BufferedOutputStream(socket.getOutputStream)

    def read_line(): Option[String] =
      try { Bytes.read_line(in).map(_.text) }
      catch { case _: SocketException => None }

    def write_line(msg: String)
    {
      require(split_lines(msg).length <= 1)
      out.write(UTF8.bytes(msg))
      out.write(10)
      try { out.flush() } catch { case _: SocketException => }
    }

    def reply(r: Server.Reply.Value, t: JSON.T)
    {
      write_line(if (t == JSON.empty) r.toString else r.toString + " " + JSON.Format(t))
    }

    def reply_ok(t: JSON.T) { reply(Server.Reply.OK, t) }
    def reply_error(t: JSON.T) { reply(Server.Reply.ERROR, t) }
    def reply_error_message(message: String, more: (String, JSON.T)*): Unit =
      reply_error(Map("message" -> message) ++ more)

    def notify(t: JSON.T) { reply(Server.Reply.NOTE, t) }
    def notify_message(message: String, more: (String, JSON.T)*): Unit =
      notify(Map("message" -> message) ++ more)
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
      {
        val connection = Connection(new Socket(InetAddress.getByName("127.0.0.1"), port))
        connection.write_line(password)
        connection
      }

      def active(): Boolean =
        try {
          using(connection())(connection =>
            {
              connection.socket.setSoTimeout(2000)
              connection.read_line() == Some(Reply.OK.toString)
            })
        }
        catch {
          case _: IOException => false
          case _: SocketException => false
          case _: SocketTimeoutException => false
        }

      def console()
      {
        using(connection())(connection =>
          {
            val tty_loop =
              new TTY_Loop(
                new BufferedWriter(new OutputStreamWriter(connection.socket.getOutputStream)),
                new BufferedReader(new InputStreamReader(connection.socket.getInputStream)))
            tty_loop.join
          })
      }
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

  def init(name: String = "", port: Int = 0): (Data.Entry, Option[Server]) =
  {
    using(SQLite.open_database(Data.database))(db =>
      {
        db.transaction {
          Isabelle_System.bash("chmod 600 " + File.bash_path(Data.database)).check
          db.create_table(Data.table)
          list(db).filterNot(_.active).foreach(entry =>
            db.using_statement(Data.table.delete(Data.name.where_equal(entry.name)))(_.execute))
        }
        db.transaction {
          find(db, name) match {
            case Some(entry) => (entry, None)
            case None =>
              val server = new Server(port)
              val entry = Data.Entry(name, server.port, server.password)

              db.using_statement(Data.table.delete(Data.name.where_equal(name)))(_.execute)
              db.using_statement(Data.table.insert())(stmt =>
              {
                stmt.string(1) = entry.name
                stmt.int(2) = entry.port
                stmt.string(3) = entry.password
                stmt.execute()
              })

              server.start
              (entry, Some(server))
          }
        }
      })
  }

  def exit(name: String = ""): Boolean =
  {
    using(SQLite.open_database(Data.database))(db =>
      db.transaction {
        find(db, name) match {
          case Some(entry) =>
            using(entry.connection())(_.write_line("shutdown"))
            while(entry.active) { Thread.sleep(50) }
            true
          case None => false
        }
      })
  }


  /* Isabelle tool wrapper */

  val isabelle_tool =
    Isabelle_Tool("server", "manage resident Isabelle servers", args =>
    {
      var console = false
      var operation_list = false
      var name = ""
      var port = 0

      val getopts =
        Getopts("""
Usage: isabelle server [OPTIONS]

  Options are:
    -C           console interaction with specified server
    -L           list servers only
    -n NAME      explicit server name
    -p PORT      explicit server port

  Manage resident Isabelle servers.
""",
          "C" -> (_ => console = true),
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
        val (entry, server) = init(name, port)
        Output.writeln(entry.toString, stdout = true)
        if (console) entry.console()
        server.foreach(_.join)
      }
    })
}

class Server private(_port: Int)
{
  server =>

  private val server_socket = new ServerSocket(_port, 50, InetAddress.getByName("127.0.0.1"))

  def close() { server_socket.close }

  def port: Int = server_socket.getLocalPort
  val password: String = Library.UUID()

  override def toString: String = Server.print(port, password)

  private def handle(connection: Server.Connection)
  {
    connection.read_line() match {
      case Some(line) if line == password =>
        connection.reply_ok(JSON.empty)
        var finished = false
        while (!finished) {
          connection.read_line() match {
            case None => finished = true
            case Some("") =>
              connection.notify_message("Command 'help' provides list of commands")
            case Some(line) =>
              val (cmd, input) = Server.split_line(line)
              Server.commands.get(cmd) match {
                case None => connection.reply_error("Bad command " + quote(cmd))
                case Some(body) =>
                  input match {
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
          }
        }
      case _ =>
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

  def start { server_thread }

  def join { server_thread.join; close() }
}
