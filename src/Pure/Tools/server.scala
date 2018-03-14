/*  Title:      Pure/Tools/server.scala
    Author:     Makarius

Resident Isabelle servers.

Message formats:
  - short message (single line):
      NAME ARGUMENT
  - long message (multiple lines):
      BYTE_LENGTH
      NAME ARGUMENT

Argument formats:
  - Unit as empty string
  - XML.Elem in YXML notation
  - JSON.T in standard notation
*/

package isabelle


import java.io.{BufferedInputStream, BufferedOutputStream, InputStreamReader, OutputStreamWriter,
  IOException}
import java.net.{Socket, SocketException, SocketTimeoutException, ServerSocket, InetAddress}


object Server
{
  /* message argument */

  object Argument
  {
    def split(msg: String): (String, String) =
    {
      val name =
        msg.takeWhile(c => Symbol.is_ascii_letter(c) || Symbol.is_ascii_letdig(c) || c == '.')
      val argument = msg.substring(name.length).dropWhile(Symbol.is_ascii_blank(_))
      (name, argument)
    }

    def print(arg: Any): String =
      arg match {
        case () => ""
        case t: XML.Elem => YXML.string_of_tree(t)
        case t: JSON.T => JSON.Format(t)
      }

    def parse(argument: String): Any =
      if (argument == "") ()
      else if (YXML.detect_elem(argument)) YXML.parse_elem(argument)
      else JSON.parse(argument, strict = false)

    def unapply(argument: String): Option[Any] =
      try { Some(parse(argument)) }
      catch { case ERROR(_) => None }
  }


  /* input command */

  object Command
  {
    type T = PartialFunction[(Context, Any), Any]

    private val table: Map[String, T] =
      Map(
        "help" -> { case (_, ()) => table.keySet.toList.sorted },
        "echo" -> { case (_, t) => t },
        "shutdown" -> { case (context, ()) => context.shutdown(); () },
        "session_build" ->
          { case (context, Server_Commands.Session_Build(args)) =>
             Server_Commands.Session_Build.command(context.progress(), args)._1
          })

    def unapply(name: String): Option[T] = table.get(name)
  }


  /* output reply */

  class Error(val message: String, val json: JSON.Object.T = JSON.Object.empty)
    extends RuntimeException(message)

  object Reply extends Enumeration
  {
    val OK, ERROR, NOTE = Value

    def message(msg: String): JSON.Object.Entry = ("message" -> msg)

    def unapply(msg: String): Option[(Reply.Value, Any)] =
    {
      if (msg == "") None
      else {
        val (name, argument) = Argument.split(msg)
        for {
          reply <-
            try { Some(withName(name)) }
            catch { case _: NoSuchElementException => None }
          arg <- Argument.unapply(argument)
        } yield (reply, arg)
      }
    }
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

    def set_timeout(t: Time) { socket.setSoTimeout(t.ms.toInt) }

    private val in = new BufferedInputStream(socket.getInputStream)
    private val out = new BufferedOutputStream(socket.getOutputStream)
    private val out_lock: AnyRef = new Object

    def tty_loop(interrupt: Option[() => Unit] = None): TTY_Loop =
      new TTY_Loop(
        new OutputStreamWriter(out),
        new InputStreamReader(in),
        writer_lock = out_lock,
        interrupt = interrupt)

    def read_message(): Option[String] =
      try {
        Bytes.read_line(in).map(_.text) match {
          case Some(Value.Int(n)) =>
            Bytes.read_block(in, n).map(bytes => Library.trim_line(bytes.text))
          case res => res
        }
      }
      catch { case _: SocketException => None }

    def write_message(msg: String): Unit = out_lock.synchronized
    {
      val b = UTF8.bytes(msg)
      if (b.length > 100 || b.contains(10)) {
        out.write(UTF8.bytes((b.length + 1).toString))
        out.write(10)
      }
      out.write(b)
      out.write(10)
      try { out.flush() } catch { case _: SocketException => }
    }

    def reply(r: Server.Reply.Value, arg: Any)
    {
      val argument = Argument.print(arg)
      write_message(if (argument == "") r.toString else r.toString + " " + argument)
    }

    def reply_ok(arg: Any) { reply(Server.Reply.OK, arg) }
    def reply_error(arg: Any) { reply(Server.Reply.ERROR, arg) }
    def reply_error_message(message: String, more: JSON.Object.Entry*): Unit =
      reply_error(JSON.Object(Reply.message(message)) ++ more)

    def notify(arg: Any) { reply(Server.Reply.NOTE, arg) }
  }


  /* context with output channels */

  class Context private[Server](server: Server, connection: Connection)
  {
    context =>

    def shutdown() { server.close() }

    def notify(arg: Any) { connection.notify(arg) }
    def message(kind: String, msg: String, more: JSON.Object.Entry*): Unit =
      notify(JSON.Object(Markup.KIND -> kind, Reply.message(msg)) ++ more)
    def writeln(msg: String, more: JSON.Object.Entry*): Unit = message(Markup.WRITELN, msg, more:_*)
    def warning(msg: String, more: JSON.Object.Entry*): Unit = message(Markup.WARNING, msg, more:_*)
    def error_message(msg: String, more: JSON.Object.Entry*): Unit =
      message(Markup.ERROR_MESSAGE, msg, more:_*)

    val logger: Connection_Logger = new Connection_Logger(context)
    def progress(): Connection_Progress = new Connection_Progress(context)

    override def toString: String = connection.toString
  }

  class Connection_Logger private[Server](context: Context) extends Logger
  {
    def apply(msg: => String): Unit = context.message(Markup.LOGGER, msg)

    override def toString: String = context.toString
  }

  class Connection_Progress private[Server](context: Context) extends Progress
  {
    override def echo(msg: String): Unit = context.writeln(msg)
    override def echo_warning(msg: String): Unit = context.warning(msg)
    override def echo_error_message(msg: String): Unit = context.error_message(msg)
    override def theory(session: String, theory: String): Unit =
      context.writeln(session + ": theory " + theory, "session" -> session, "theory" -> theory)

    @volatile private var is_stopped = false
    override def stopped: Boolean = is_stopped
    def stop { is_stopped = true }

    override def toString: String = context.toString
  }


  /* server info */

  sealed case class Info(name: String, port: Int, password: String)
  {
    override def toString: String =
      "server " + quote(name) + " = " + print(port, password)

    def connection(): Connection =
    {
      val connection = Connection(new Socket(InetAddress.getByName("127.0.0.1"), port))
      connection.write_message(password)
      connection
    }

    def active(): Boolean =
      try {
        using(connection())(connection =>
          {
            connection.set_timeout(Time.seconds(2.0))
            connection.read_message() == Some(Reply.OK.toString)
          })
      }
      catch {
        case _: IOException => false
        case _: SocketException => false
        case _: SocketTimeoutException => false
      }
  }


  /* per-user servers */

  val default_name = "isabelle"

  def print(port: Int, password: String): String =
    "127.0.0.1:" + port + " (password " + quote(password) + ")"

  object Data
  {
    val database = Path.explode("$ISABELLE_HOME_USER/servers.db")

    val name = SQL.Column.string("name").make_primary_key
    val port = SQL.Column.int("port")
    val password = SQL.Column.string("password")
    val table = SQL.Table("isabelle_servers", List(name, port, password))
  }

  def list(db: SQLite.Database): List[Info] =
    if (db.tables.contains(Data.table.name)) {
      db.using_statement(Data.table.select())(stmt =>
        stmt.execute_query().iterator(res =>
          Info(
            res.string(Data.name),
            res.int(Data.port),
            res.string(Data.password))).toList.sortBy(_.name))
    }
    else Nil

  def find(db: SQLite.Database, name: String): Option[Info] =
    list(db).find(server_info => server_info.name == name && server_info.active)

  def init(name: String = default_name, port: Int = 0, existing_server: Boolean = false)
    : (Info, Option[Server]) =
  {
    using(SQLite.open_database(Data.database))(db =>
      {
        db.transaction {
          Isabelle_System.bash("chmod 600 " + File.bash_path(Data.database)).check
          db.create_table(Data.table)
          list(db).filterNot(_.active).foreach(server_info =>
            db.using_statement(Data.table.delete(Data.name.where_equal(server_info.name)))(
              _.execute))
        }
        db.transaction {
          find(db, name) match {
            case Some(server_info) => (server_info, None)
            case None =>
              if (existing_server) error("Isabelle server " + quote(name) + " not running")

              val server = new Server(port)
              val server_info = Info(name, server.port, server.password)

              db.using_statement(Data.table.delete(Data.name.where_equal(name)))(_.execute)
              db.using_statement(Data.table.insert())(stmt =>
              {
                stmt.string(1) = server_info.name
                stmt.int(2) = server_info.port
                stmt.string(3) = server_info.password
                stmt.execute()
              })

              server.start
              (server_info, Some(server))
          }
        }
      })
  }

  def exit(name: String = default_name): Boolean =
  {
    using(SQLite.open_database(Data.database))(db =>
      db.transaction {
        find(db, name) match {
          case Some(server_info) =>
            using(server_info.connection())(_.write_message("shutdown"))
            while(server_info.active) { Thread.sleep(50) }
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
      var operation_exit = false
      var name = default_name
      var port = 0
      var existing_server = false

      val getopts =
        Getopts("""
Usage: isabelle server [OPTIONS]

  Options are:
    -C           console interaction with specified server
    -L           list servers (exclusive operation)
    -X           exit specified server (exclusive operation)
    -n NAME      explicit server name (default: """ + default_name + """)
    -p PORT      explicit server port
    -s           assume existing server, no implicit startup

  Manage resident Isabelle servers.
""",
          "C" -> (_ => console = true),
          "L" -> (_ => operation_list = true),
          "X" -> (_ => operation_exit = true),
          "n:" -> (arg => name = arg),
          "p:" -> (arg => port = Value.Int.parse(arg)),
          "s" -> (_ => existing_server = true))

      val more_args = getopts(args)
      if (more_args.nonEmpty) getopts.usage()

      if (operation_list) {
        for {
          server_info <- using(SQLite.open_database(Data.database))(list(_))
          if server_info.active
        } Output.writeln(server_info.toString, stdout = true)
      }
      else if (operation_exit) {
        val ok = Server.exit(name)
        sys.exit(if (ok) 0 else 1)
      }
      else {
        val (server_info, server) = init(name, port = port, existing_server = existing_server)
        Output.writeln(server_info.toString, stdout = true)
        if (console) {
          using(server_info.connection())(connection => connection.tty_loop().join)
        }
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
    val context = new Server.Context(server, connection)

    connection.read_message() match {
      case Some(msg) if msg == password =>
        connection.reply_ok(())
        var finished = false
        while (!finished) {
          connection.read_message() match {
            case None => finished = true
            case Some("") => context.notify("Command 'help' provides list of commands")
            case Some(msg) =>
              val (name, argument) = Server.Argument.split(msg)
              name match {
                case Server.Command(cmd) =>
                  argument match {
                    case Server.Argument(arg) =>
                      if (cmd.isDefinedAt((context, arg))) {
                        Exn.capture { cmd((context, arg)) } match {
                          case Exn.Res(res) => connection.reply_ok(res)
                          case Exn.Exn(exn: Server.Error) =>
                            connection.reply_error_message(exn.message, exn.json.toList:_*)
                          case Exn.Exn(ERROR(msg)) =>
                            connection.reply_error_message(msg)
                          case Exn.Exn(exn) => throw exn
                        }
                      }
                      else {
                        connection.reply_error_message(
                          "Bad argument for command " + Library.single_quote(name),
                          "argument" -> argument)
                      }
                    case _ =>
                      connection.reply_error_message(
                        "Malformed argument for command " + Library.single_quote(name),
                        "argument" -> argument)
                  }
                case _ => connection.reply_error("Bad command " + Library.single_quote(name))
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
