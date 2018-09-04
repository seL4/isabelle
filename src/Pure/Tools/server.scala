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
      val name = msg.takeWhile(is_name_char(_))
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
        "shutdown" -> { case (context, ()) => context.server.shutdown() },
        "cancel" ->
          { case (context, Server_Commands.Cancel(args)) => context.cancel_task(args.task) },
        "session_build" ->
          { case (context, Server_Commands.Session_Build(args)) =>
              context.make_task(task =>
                Server_Commands.Session_Build.command(args, progress = task.progress)._1)
          },
        "session_start" ->
          { case (context, Server_Commands.Session_Start(args)) =>
              context.make_task(task =>
                {
                  val (res, entry) =
                    Server_Commands.Session_Start.command(
                      args, progress = task.progress, log = context.server.log)
                  context.server.add_session(entry)
                  res
                })
          },
        "session_stop" ->
          { case (context, Server_Commands.Session_Stop(id)) =>
              context.make_task(_ =>
                {
                  val session = context.server.remove_session(id)
                  Server_Commands.Session_Stop.command(session)._1
                })
          },
        "use_theories" ->
          { case (context, Server_Commands.Use_Theories(args)) =>
              context.make_task(task =>
                {
                  val session = context.server.the_session(args.session_id)
                  Server_Commands.Use_Theories.command(
                    args, session, id = task.id, progress = task.progress)._1
                })
          },
        "purge_theories" ->
          { case (context, Server_Commands.Purge_Theories(args)) =>
              val session = context.server.the_session(args.session_id)
              Server_Commands.Purge_Theories.command(args, session)._1
          })

    def unapply(name: String): Option[T] = table.get(name)
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

    def reply(r: Reply.Value, arg: Any)
    {
      val argument = Argument.print(arg)
      write_message(if (argument == "") r.toString else r.toString + " " + argument)
    }

    def reply_ok(arg: Any) { reply(Reply.OK, arg) }
    def reply_error(arg: Any) { reply(Reply.ERROR, arg) }
    def reply_error_message(message: String, more: JSON.Object.Entry*): Unit =
      reply_error(Reply.error_message(message) ++ more)

    def notify(arg: Any) { reply(Reply.NOTE, arg) }
  }


  /* context with output channels */

  class Context private[Server](val server: Server, connection: Connection)
  {
    context =>

    def reply(r: Reply.Value, arg: Any) { connection.reply(r, arg) }
    def notify(arg: Any) { connection.notify(arg) }
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

    def cancel_task(id: UUID): Unit =
      _tasks.change(tasks => { tasks.find(task => task.id == id).foreach(_.cancel); tasks })

    def close()
    {
      while(_tasks.change_result(tasks => { tasks.foreach(_.cancel); (tasks.nonEmpty, tasks) }))
      { _tasks.value.foreach(_.join) }
    }
  }

  class Connection_Progress private[Server](context: Context, more: JSON.Object.Entry*)
    extends Progress
  {
    override def echo(msg: String): Unit = context.writeln(msg, more:_*)
    override def echo_warning(msg: String): Unit = context.warning(msg, more:_*)
    override def echo_error_message(msg: String): Unit = context.error_message(msg, more:_*)

    override def theory(session: String, theory: String): Unit =
      context.writeln(Progress.theory_message(session, theory),
        (List("session" -> session, "theory" -> theory) ::: more.toList):_*)

    override def nodes_status(nodes_status: Document_Status.Nodes_Status)
    {
      val json =
        for ((name, node_status) <- nodes_status.present)
          yield name.json + ("status" -> nodes_status(name).json)
      context.notify(JSON.Object(Markup.KIND -> Markup.NODES_STATUS, Markup.NODES_STATUS -> json))
    }

    @volatile private var is_stopped = false
    override def stopped: Boolean = is_stopped
    def stop { is_stopped = true }

    override def toString: String = context.toString
  }

  class Task private[Server](val context: Context, body: Task => JSON.Object.T)
  {
    task =>

    val id: UUID = UUID()
    val ident: JSON.Object.Entry = ("task" -> id.toString)

    val progress: Connection_Progress = context.progress(ident)
    def cancel { progress.stop }

    private lazy val thread = Standard_Thread.fork("server_task")
    {
      Exn.capture { body(task) } match {
        case Exn.Res(res) =>
          context.reply(Reply.FINISHED, res + ident)
        case Exn.Exn(exn) =>
          val err = json_error(exn)
          if (err.isEmpty) throw exn else context.reply(Reply.FAILED, err + ident)
      }
      progress.stop
      context.remove_task(task)
    }
    def start { thread }
    def join { thread.join }
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
            connection.read_message() match {
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

  def init(
    name: String = default_name,
    port: Int = 0,
    existing_server: Boolean = false,
    log: Logger = No_Logger): (Info, Option[Server]) =
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

              val server = new Server(port, log)
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
          server_info <- using(SQLite.open_database(Data.database))(list(_))
          if server_info.active
        } Output.writeln(server_info.toString, stdout = true)
      }
      else if (operation_exit) {
        val ok = Server.exit(name)
        sys.exit(if (ok) 0 else 1)
      }
      else {
        val log = Logger.make(log_file)
        val (server_info, server) =
          init(name, port = port, existing_server = existing_server, log = log)
        Output.writeln(server_info.toString, stdout = true)
        if (console) {
          using(server_info.connection())(connection => connection.tty_loop().join)
        }
        server.foreach(_.join)
      }
    })
}

class Server private(_port: Int, val log: Logger)
{
  server =>

  private val server_socket = new ServerSocket(_port, 50, InetAddress.getByName("127.0.0.1"))

  private val _sessions = Synchronized(Map.empty[UUID, Thy_Resources.Session])
  def err_session(id: UUID): Nothing = error("No session " + Library.single_quote(id.toString))
  def the_session(id: UUID): Thy_Resources.Session =
    _sessions.value.get(id) getOrElse err_session(id)
  def add_session(entry: (UUID, Thy_Resources.Session)) { _sessions.change(_ + entry) }
  def remove_session(id: UUID): Thy_Resources.Session =
  {
    _sessions.change_result(sessions =>
      sessions.get(id) match {
        case Some(session) => (session, sessions - id)
        case None => err_session(id)
      })
  }

  def shutdown()
  {
    server_socket.close

    val sessions = _sessions.change_result(sessions => (sessions, Map.empty))
    for ((_, session) <- sessions) {
      try {
        val result = session.stop()
        if (!result.ok) log("Session shutdown failed: return code " + result.rc)
      }
      catch { case ERROR(msg) => log("Session shutdown failed: " + msg) }
    }
  }

  def port: Int = server_socket.getLocalPort
  val password: String = UUID().toString

  override def toString: String = Server.print(port, password)

  private def handle(connection: Server.Connection)
  {
    using(new Server.Context(server, connection))(context =>
    {
      connection.read_message() match {
        case Some(msg) if msg == password =>
          connection.reply_ok(
            JSON.Object(
              "isabelle_id" -> Isabelle_System.isabelle_id(),
              "isabelle_version" -> Distribution.version))

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
                            case Exn.Res(task: Server.Task) =>
                              connection.reply_ok(JSON.Object(task.ident))
                              task.start
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
                  case _ => connection.reply_error("Bad command " + Library.single_quote(name))
                }
            }
          }
        case _ =>
      }
    })
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

  def join { server_thread.join; shutdown() }
}
