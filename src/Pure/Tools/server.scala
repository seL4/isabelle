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
    def is_name_char(c: Char): Boolean =
      Symbol.is_ascii_letter(c) || Symbol.is_ascii_digit(c) || c == '_' || c == '.'

    def split(msg: String): (String, String) =
    {
      val name = msg.takeWhile(is_name_char)
      val argument = msg.substring(name.length).dropWhile(Symbol.is_ascii_blank)
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

  type Command_Body = PartialFunction[(Context, Any), Any]

  abstract class Command(val command_name: String)
  {
    def command_body: Command_Body
    override def toString: String = command_name
  }

  class Commands(commands: Command*) extends Isabelle_System.Service
  {
    def entries: List[Command] = commands.toList
  }

  private lazy val command_table: Map[String, Command] =
    Isabelle_System.make_services(classOf[Commands]).flatMap(_.entries).
      foldLeft(Map.empty[String, Command]) {
        case (cmds, cmd) =>
          val name = cmd.command_name
          if (cmds.isDefinedAt(name)) error("Duplicate Isabelle server command: " + quote(name))
          else cmds + (name -> cmd)
      }


  /* output reply */

  class Error(val message: String, val json: JSON.Object.T = JSON.Object.empty)
    extends RuntimeException(message)

  def json_error(exn: Throwable): JSON.Object.T =
    exn match {
      case e: Error => Reply.error_message(e.message) ++ e.json
      case ERROR(msg) => Reply.error_message(msg)
      case _ if Exn.is_interrupt(exn) => Reply.error_message(Exn.message(exn))
      case _ => JSON.Object.empty
    }

  object Reply extends Enumeration
  {
    val OK, ERROR, FINISHED, FAILED, NOTE = Value

    def message(msg: String, kind: String = ""): JSON.Object.T =
      JSON.Object(Markup.KIND -> proper_string(kind).getOrElse(Markup.WRITELN), "message" -> msg)

    def error_message(msg: String): JSON.Object.T =
      message(msg, kind = Markup.ERROR)

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


  /* handler: port, password, thread */

  abstract class Handler(port0: Int)
  {
    val socket: ServerSocket = new ServerSocket(port0, 50, Server.localhost)
    def port: Int = socket.getLocalPort
    val password: String = UUID.random().toString

    override def toString: String = print(port, password)

    def handle(connection: Server.Connection): Unit

    private lazy val thread: Thread =
      Isabelle_Thread.fork(name = "server_handler") {
        var finished = false
        while (!finished) {
          Exn.capture(socket.accept) match {
            case Exn.Res(client) =>
              Isabelle_Thread.fork(name = "client") {
                using(Connection(client))(connection =>
                  if (connection.read_password(password)) handle(connection))
              }
            case Exn.Exn(_) => finished = true
          }
        }
      }

    def start(): Unit = thread
    def join(): Unit = thread.join()
    def stop(): Unit = { socket.close(); join() }
  }


  /* socket connection */

  object Connection
  {
    def apply(socket: Socket): Connection =
      new Connection(socket)
  }

  class Connection private(socket: Socket) extends AutoCloseable
  {
    override def toString: String = socket.toString

    def close(): Unit = socket.close()

    def set_timeout(t: Time): Unit = socket.setSoTimeout(t.ms.toInt)

    private val in = new BufferedInputStream(socket.getInputStream)
    private val out = new BufferedOutputStream(socket.getOutputStream)
    private val out_lock: AnyRef = new Object

    def tty_loop(): TTY_Loop =
      new TTY_Loop(
        new OutputStreamWriter(out),
        new InputStreamReader(in),
        writer_lock = out_lock)

    def read_password(password: String): Boolean =
      try { Byte_Message.read_line(in).map(_.text) == Some(password) }
      catch { case _: IOException => false }

    def read_line_message(): Option[String] =
      try { Byte_Message.read_line_message(in).map(_.text) }
      catch { case _: IOException => None }

    def await_close(): Unit =
      try { Byte_Message.read(in, 1); socket.close() }
      catch { case _: IOException => }

    def write_line_message(msg: String): Unit =
      out_lock.synchronized { Byte_Message.write_line_message(out, Bytes(UTF8.bytes(msg))) }

    def reply(r: Reply.Value, arg: Any): Unit =
    {
      val argument = Argument.print(arg)
      write_line_message(if (argument == "") r.toString else r.toString + " " + argument)
    }

    def reply_ok(arg: Any): Unit = reply(Reply.OK, arg)
    def reply_error(arg: Any): Unit = reply(Reply.ERROR, arg)
    def reply_error_message(message: String, more: JSON.Object.Entry*): Unit =
      reply_error(Reply.error_message(message) ++ more)

    def notify(arg: Any): Unit = reply(Reply.NOTE, arg)
  }


  /* context with output channels */

  class Context private[Server](val server: Server, connection: Connection)
    extends AutoCloseable
  {
    context =>

    def command_list: List[String] = command_table.keys.toList.sorted

    def reply(r: Reply.Value, arg: Any): Unit = connection.reply(r, arg)
    def notify(arg: Any): Unit = connection.notify(arg)
    def message(kind: String, msg: String, more: JSON.Object.Entry*): Unit =
      notify(Reply.message(msg, kind = kind) ++ more)
    def writeln(msg: String, more: JSON.Object.Entry*): Unit = message(Markup.WRITELN, msg, more:_*)
    def warning(msg: String, more: JSON.Object.Entry*): Unit = message(Markup.WARNING, msg, more:_*)
    def error_message(msg: String, more: JSON.Object.Entry*): Unit =
      message(Markup.ERROR, msg, more:_*)

    def progress(more: JSON.Object.Entry*): Connection_Progress =
      new Connection_Progress(context, more:_*)

    override def toString: String = connection.toString


    /* asynchronous tasks */

    private val _tasks = Synchronized(Set.empty[Task])

    def make_task(body: Task => JSON.Object.T): Task =
    {
      val task = new Task(context, body)
      _tasks.change(_ + task)
      task
    }

    def remove_task(task: Task): Unit =
      _tasks.change(_ - task)

    def cancel_task(id: UUID.T): Unit =
      _tasks.change(tasks => { tasks.find(task => task.id == id).foreach(_.cancel()); tasks })

    def close(): Unit =
    {
      while(_tasks.change_result(tasks => { tasks.foreach(_.cancel()); (tasks.nonEmpty, tasks) }))
      { _tasks.value.foreach(_.join()) }
    }
  }

  class Connection_Progress private[Server](context: Context, more: JSON.Object.Entry*)
    extends Progress
  {
    override def echo(msg: String): Unit = context.writeln(msg, more:_*)
    override def echo_warning(msg: String): Unit = context.warning(msg, more:_*)
    override def echo_error_message(msg: String): Unit = context.error_message(msg, more:_*)

    override def theory(theory: Progress.Theory): Unit =
    {
      val entries: List[JSON.Object.Entry] =
        List("theory" -> theory.theory, "session" -> theory.session) :::
          (theory.percentage match { case None => Nil case Some(p) => List("percentage" -> p) })
      context.writeln(theory.message, entries ::: more.toList:_*)
    }

    override def nodes_status(nodes_status: Document_Status.Nodes_Status): Unit =
    {
      val json =
        for ((name, node_status) <- nodes_status.present)
          yield name.json + ("status" -> node_status.json)
      context.notify(JSON.Object(Markup.KIND -> Markup.NODES_STATUS, Markup.NODES_STATUS -> json))
    }

    override def toString: String = context.toString
  }

  class Task private[Server](val context: Context, body: Task => JSON.Object.T)
  {
    task =>

    val id: UUID.T = UUID.random()
    val ident: JSON.Object.Entry = ("task" -> id.toString)

    val progress: Connection_Progress = context.progress(ident)
    def cancel(): Unit = progress.stop()

    private lazy val thread = Isabelle_Thread.fork(name = "server_task")
    {
      Exn.capture { body(task) } match {
        case Exn.Res(res) =>
          context.reply(Reply.FINISHED, res + ident)
        case Exn.Exn(exn) =>
          val err = json_error(exn)
          if (err.isEmpty) throw exn else context.reply(Reply.FAILED, err + ident)
      }
      progress.stop()
      context.remove_task(task)
    }
    def start(): Unit = thread
    def join(): Unit = thread.join()
  }


  /* server info */

  val localhost_name: String = "127.0.0.1"
  def localhost: InetAddress = InetAddress.getByName(localhost_name)

  def print_address(port: Int): String = localhost_name + ":" + port

  def print(port: Int, password: String): String =
    print_address(port) + " (password " + quote(password) + ")"

  object Info
  {
    private val Pattern =
      ("""server "([^"]*)" = \Q""" + localhost_name + """\E:(\d+) \(password "([^"]*)"\)""").r

    def parse(s: String): Option[Info] =
      s match {
        case Pattern(name, Value.Int(port), password) => Some(Info(name, port, password))
        case _ => None
      }

    def apply(name: String, port: Int, password: String): Info =
      new Info(name, port, password)
  }

  class Info private(val name: String, val port: Int, val password: String)
  {
    def address: String = print_address(port)

    override def toString: String =
      "server " + quote(name) + " = " + print(port, password)

    def connection(): Connection =
    {
      val connection = Connection(new Socket(localhost, port))
      connection.write_line_message(password)
      connection
    }

    def active: Boolean =
      try {
        using(connection())(connection =>
          {
            connection.set_timeout(Time.seconds(2.0))
            connection.read_line_message() match {
              case Some(Reply(Reply.OK, _)) => true
              case _ => false
            }
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

  def init(
    name: String = default_name,
    port: Int = 0,
    existing_server: Boolean = false,
    log: Logger = No_Logger): (Info, Option[Server]) =
  {
    using(SQLite.open_database(Data.database))(db =>
      {
        db.transaction {
          Isabelle_System.chmod("600", Data.database)
          db.create_table(Data.table)
          list(db).filterNot(_.active).foreach(server_info =>
            db.using_statement(Data.table.delete(Data.name.where_equal(server_info.name)))(
              _.execute()))
        }
        db.transaction {
          find(db, name) match {
            case Some(server_info) => (server_info, None)
            case None =>
              if (existing_server) error("Isabelle server " + quote(name) + " not running")

              val server = new Server(port, log)
              val server_info = Info(name, server.port, server.password)

              db.using_statement(Data.table.delete(Data.name.where_equal(name)))(_.execute())
              db.using_statement(Data.table.insert())(stmt =>
              {
                stmt.string(1) = server_info.name
                stmt.int(2) = server_info.port
                stmt.string(3) = server_info.password
                stmt.execute()
              })

              server.start()
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
            using(server_info.connection())(_.write_line_message("shutdown"))
            while(server_info.active) { Time.seconds(0.05).sleep() }
            true
          case None => false
        }
      })
  }


  /* Isabelle tool wrapper */

  val isabelle_tool =
    Isabelle_Tool("server", "manage resident Isabelle servers", Scala_Project.here, args =>
    {
      var console = false
      var log_file: Option[Path] = None
      var operation_list = false
      var operation_exit = false
      var name = default_name
      var port = 0
      var existing_server = false

      val getopts =
        Getopts("""
Usage: isabelle server [OPTIONS]

  Options are:
    -L FILE      logging on FILE
    -c           console interaction with specified server
    -l           list servers (alternative operation)
    -n NAME      explicit server name (default: """ + default_name + """)
    -p PORT      explicit server port
    -s           assume existing server, no implicit startup
    -x           exit specified server (alternative operation)

  Manage resident Isabelle servers.
""",
          "L:" -> (arg => log_file = Some(Path.explode(File.standard_path(arg)))),
          "c" -> (_ => console = true),
          "l" -> (_ => operation_list = true),
          "n:" -> (arg => name = arg),
          "p:" -> (arg => port = Value.Int.parse(arg)),
          "s" -> (_ => existing_server = true),
          "x" -> (_ => operation_exit = true))

      val more_args = getopts(args)
      if (more_args.nonEmpty) getopts.usage()

      if (operation_list) {
        for {
          server_info <- using(SQLite.open_database(Data.database))(list)
          if server_info.active
        } Output.writeln(server_info.toString, stdout = true)
      }
      else if (operation_exit) {
        val ok = Server.exit(name)
        sys.exit(if (ok) 0 else 2)
      }
      else {
        val log = Logger.make(log_file)
        val (server_info, server) =
          init(name, port = port, existing_server = existing_server, log = log)
        Output.writeln(server_info.toString, stdout = true)
        if (console) {
          using(server_info.connection())(connection => connection.tty_loop().join())
        }
        server.foreach(_.join())
      }
    })
}

class Server private(port0: Int, val log: Logger) extends Server.Handler(port0)
{
  server =>

  private val _sessions = Synchronized(Map.empty[UUID.T, Headless.Session])
  def err_session(id: UUID.T): Nothing = error("No session " + Library.single_quote(id.toString))
  def the_session(id: UUID.T): Headless.Session = _sessions.value.getOrElse(id, err_session(id))
  def add_session(entry: (UUID.T, Headless.Session)): Unit = _sessions.change(_ + entry)
  def remove_session(id: UUID.T): Headless.Session =
  {
    _sessions.change_result(sessions =>
      sessions.get(id) match {
        case Some(session) => (session, sessions - id)
        case None => err_session(id)
      })
  }

  def shutdown(): Unit =
  {
    server.socket.close()

    val sessions = _sessions.change_result(sessions => (sessions, Map.empty))
    for ((_, session) <- sessions) {
      try {
        val result = session.stop()
        if (!result.ok) log("Session shutdown failed: " + result.print_rc)
      }
      catch { case ERROR(msg) => log("Session shutdown failed: " + msg) }
    }
  }

  override def join(): Unit = { super.join(); shutdown() }

  override def handle(connection: Server.Connection): Unit =
  {
    using(new Server.Context(server, connection))(context =>
    {
      connection.reply_ok(
        JSON.Object(
          "isabelle_id" -> Isabelle_System.isabelle_id(),
          "isabelle_name" -> Isabelle_System.isabelle_name()))

      var finished = false
      while (!finished) {
        connection.read_line_message() match {
          case None => finished = true
          case Some("") => context.notify("Command 'help' provides list of commands")
          case Some(msg) =>
            val (name, argument) = Server.Argument.split(msg)
            Server.command_table.get(name) match {
              case Some(cmd) =>
                argument match {
                  case Server.Argument(arg) =>
                    if (cmd.command_body.isDefinedAt((context, arg))) {
                      Exn.capture { cmd.command_body((context, arg)) } match {
                        case Exn.Res(task: Server.Task) =>
                          connection.reply_ok(JSON.Object(task.ident))
                          task.start()
                        case Exn.Res(res) => connection.reply_ok(res)
                        case Exn.Exn(exn) =>
                          val err = Server.json_error(exn)
                          if (err.isEmpty) throw exn else connection.reply_error(err)
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
              case None => connection.reply_error("Bad command " + Library.single_quote(name))
            }
        }
      }
    })
  }
}
