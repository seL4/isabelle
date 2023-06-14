/*  Title:      Pure/System/progress.scala
    Author:     Makarius

Progress context for system processes.
*/

package isabelle


import java.util.{Map => JMap}
import java.io.{File => JFile}

import scala.collection.immutable.SortedMap


object Progress {
  /* messages */

  object Kind extends Enumeration { val writeln, warning, error_message = Value }
  sealed case class Message(kind: Kind.Value, text: String, verbose: Boolean = false) {
    def output_text: String =
      kind match {
        case Kind.writeln => Output.writeln_text(text)
        case Kind.warning => Output.warning_text(text)
        case Kind.error_message => Output.error_message_text(text)
      }

    override def toString: String = output_text
  }

  sealed case class Theory(theory: String, session: String = "", percentage: Option[Int] = None) {
    def message: Message =
      Message(Kind.writeln, print_session + print_theory + print_percentage, verbose = true)

    def print_session: String = if_proper(session, session + ": ")
    def print_theory: String = "theory " + theory
    def print_percentage: String =
      percentage match { case None => "" case Some(p) => " " + p + "%" }
  }


  /* SQL data model */

  object Data {
    def make_table(name: String, columns: List[SQL.Column], body: String = ""): SQL.Table =
      SQL.Table("isabelle_progress" + if_proper(name, "_" + name), columns, body = body)

    object Base {
      val context_uuid = SQL.Column.string("context_uuid").make_primary_key
      val context = SQL.Column.long("context").make_primary_key
      val stopped = SQL.Column.bool("stopped")

      val table = make_table("", List(context_uuid, context, stopped))
    }

    object Agents {
      val agent_uuid = SQL.Column.string("agent_uuid").make_primary_key
      val context_uuid = SQL.Column.string("context_uuid").make_primary_key
      val hostname = SQL.Column.string("hostname")
      val java_pid = SQL.Column.long("java_pid")
      val java_start = SQL.Column.date("java_start")
      val start = SQL.Column.date("start")
      val stamp = SQL.Column.date("stamp")
      val stop = SQL.Column.date("stop")
      val seen = SQL.Column.long("seen")

      val table = make_table("agents",
        List(agent_uuid, context_uuid, hostname, java_pid, java_start, start, stamp, stop, seen))
    }

    object Messages {
      type T = SortedMap[Long, Message]
      val empty: T = SortedMap.empty

      val context = SQL.Column.long("context").make_primary_key
      val serial = SQL.Column.long("serial").make_primary_key
      val kind = SQL.Column.int("kind")
      val text = SQL.Column.string("text")
      val verbose = SQL.Column.bool("verbose")

      val table = make_table("messages", List(context, serial, kind, text, verbose))
    }

    val all_tables: SQL.Tables = SQL.Tables(Base.table, Agents.table, Messages.table)

    def read_progress_context(db: SQL.Database, context_uuid: String): Option[Long] =
      db.execute_query_statementO(
        Base.table.select(List(Base.context),
          sql = Base.context_uuid.where_equal(context_uuid)), _.long(Base.context))

    def next_progress_context(db: SQL.Database): Long =
      db.execute_query_statementO(
        Base.table.select(List(Base.context.max)), _.long(Base.context)).getOrElse(0L) + 1L

    def read_progress_stopped(db: SQL.Database, context: Long): Boolean =
      db.execute_query_statementO(
        Base.table.select(List(Base.stopped), sql = Base.context.where_equal(context)),
        _.bool(Base.stopped)
      ).getOrElse(false)

    def write_progress_stopped(db: SQL.Database, context: Long, stopped: Boolean): Unit =
      db.execute_statement(
        Base.table.update(List(Base.stopped), sql = Base.context.where_equal(context)),
          body = { stmt => stmt.bool(1) = stopped })

    def update_agent(
      db: SQL.Database,
      agent_uuid: String,
      seen: Long,
      stop: Boolean = false
    ): Unit = {
      val sql =
        Agents.table.update(List(Agents.stamp, Agents.stop, Agents.seen),
          sql = Agents.agent_uuid.where_equal(agent_uuid))
      db.execute_statement(sql, body = { stmt =>
        val now = db.now()
        stmt.date(1) = now
        stmt.date(2) = if (stop) Some(now) else None
        stmt.long(3) = seen
      })
    }

    def next_messages_serial(db: SQL.Database, context: Long): Long =
      db.execute_query_statementO(
        Messages.table.select(
          List(Messages.serial.max), sql = Base.context.where_equal(context)),
        _.long(Messages.serial)
      ).getOrElse(0L) + 1L

    def read_messages(db: SQL.Database, context: Long, seen: Long = 0): Messages.T =
      db.execute_query_statement(
        Messages.table.select(
          List(Messages.serial, Messages.kind, Messages.text, Messages.verbose),
          sql =
            SQL.where_and(
              Messages.context.ident + " = " + context,
              if (seen <= 0) "" else Messages.serial.ident + " > " + seen)),
        SortedMap.from[Long, Message],
        { res =>
          val serial = res.long(Messages.serial)
          val kind = Kind(res.int(Messages.kind))
          val text = res.string(Messages.text)
          val verbose = res.bool(Messages.verbose)
          serial -> Message(kind, text, verbose = verbose)
        }
      )

    def write_messages(
      db: SQL.Database,
      context: Long,
      serial: Long,
      message: Message
    ): Unit = {
      db.execute_statement(Messages.table.insert(), body = { stmt =>
        stmt.long(1) = context
        stmt.long(2) = serial
        stmt.int(3) = message.kind.id
        stmt.string(4) = message.text
        stmt.bool(5) = message.verbose
      })
    }
  }
}

class Progress {
  def verbose: Boolean = false
  final def do_output(message: Progress.Message): Boolean = !message.verbose || verbose

  def output(message: Progress.Message) = {}

  final def echo(msg: String, verbose: Boolean = false): Unit =
    output(Progress.Message(Progress.Kind.writeln, msg, verbose = verbose))
  final def echo_warning(msg: String, verbose: Boolean = false): Unit =
    output(Progress.Message(Progress.Kind.warning, msg, verbose = verbose))
  final def echo_error_message(msg: String, verbose: Boolean = false): Unit =
    output(Progress.Message(Progress.Kind.error_message, msg, verbose = verbose))

  final def echo_if(cond: Boolean, msg: String): Unit = if (cond) echo(msg)

  def theory(theory: Progress.Theory): Unit = output(theory.message)
  def nodes_status(nodes_status: Document_Status.Nodes_Status): Unit = {}

  final def timeit[A](
    body: => A,
    message: Exn.Result[A] => String = null,
    enabled: Boolean = true
  ): A = Timing.timeit(body, message = message, enabled = enabled, output = echo(_))

  @volatile private var is_stopped = false
  def stop(): Unit = { is_stopped = true }
  def stopped: Boolean = {
    if (Thread.interrupted()) is_stopped = true
    is_stopped
  }

  final def interrupt_handler[A](e: => A): A = POSIX_Interrupt.handler { stop() } { e }
  final def expose_interrupt(): Unit = if (stopped) throw Exn.Interrupt()
  override def toString: String = if (stopped) "Progress(stopped)" else "Progress"

  final def bash(script: String,
    cwd: JFile = null,
    env: JMap[String, String] = Isabelle_System.settings(),
    redirect: Boolean = false,
    echo: Boolean = false,
    watchdog: Time = Time.zero,
    strict: Boolean = true
  ): Process_Result = {
    val result =
      Isabelle_System.bash(script, cwd = cwd, env = env, redirect = redirect,
        progress_stdout = echo_if(echo, _),
        progress_stderr = echo_if(echo, _),
        watchdog = if (watchdog.is_zero) None else Some((watchdog, _ => stopped)),
        strict = strict)
    if (strict && stopped) throw Exn.Interrupt() else result
  }
}

class Console_Progress(override val verbose: Boolean = false, stderr: Boolean = false)
extends Progress {
  override def output(message: Progress.Message): Unit =
    if (do_output(message)) {
      Output.output(message.output_text, stdout = !stderr, include_empty = true)
    }

  override def toString: String = super.toString + ": console"
}

class File_Progress(path: Path, override val verbose: Boolean = false)
extends Progress {
  override def output(message: Progress.Message): Unit =
    if (do_output(message)) File.append(path, message.output_text + "\n")

  override def toString: String = super.toString + ": " + path.toString
}


/* database progress */

class Database_Progress(
  val db: SQL.Database,
  val base_progress: Progress,
  val hostname: String = Isabelle_System.hostname(),
  val context_uuid: String = UUID.random().toString)
extends Progress {
  database_progress =>

  private var _agent_uuid: String = ""
  private var _context: Long = 0
  private var _seen: Long = 0

  def agent_uuid: String = synchronized { _agent_uuid }

  private def transaction_lock[A](body: => A, create: Boolean = false): A =
    db.transaction_lock(Progress.Data.all_tables, create = create)(body)

  private def init(): Unit = synchronized {
    transaction_lock(create = true, body = {
      Progress.Data.read_progress_context(db, context_uuid) match {
        case Some(context) =>
          _context = context
          _agent_uuid = UUID.random().toString
        case None =>
          _context = Progress.Data.next_progress_context(db)
          _agent_uuid = context_uuid
          db.execute_statement(Progress.Data.Base.table.insert(), { stmt =>
            stmt.string(1) = context_uuid
            stmt.long(2) = _context
            stmt.bool(3) = false
          })
      }
      db.execute_statement(Progress.Data.Agents.table.insert(), { stmt =>
        val java = ProcessHandle.current()
        val java_pid = java.pid
        val java_start = Date.instant(java.info.startInstant.get)
        val now = db.now()

        stmt.string(1) = _agent_uuid
        stmt.string(2) = context_uuid
        stmt.string(3) = hostname
        stmt.long(4) = java_pid
        stmt.date(5) = java_start
        stmt.date(6) = now
        stmt.date(7) = now
        stmt.date(8) = None
        stmt.long(9) = 0L
      })
    })
    if (context_uuid == _agent_uuid) db.vacuum(Progress.Data.all_tables)
  }

  def exit(): Unit = synchronized {
    if (_context > 0) {
      transaction_lock {
        Progress.Data.update_agent(db, _agent_uuid, _seen, stop = true)
      }
      _context = 0
    }
  }

  private def sync_database[A](body: => A): A = synchronized {
    require(_context > 0)
    transaction_lock {
      val stopped_db = Progress.Data.read_progress_stopped(db, _context)
      val stopped = base_progress.stopped

      if (stopped_db && !stopped) base_progress.stop()
      if (stopped && !stopped_db) Progress.Data.write_progress_stopped(db, _context, true)

      val messages = Progress.Data.read_messages(db, _context, seen = _seen)
      for ((seen, message) <- messages) {
        if (base_progress.do_output(message)) base_progress.output(message)
        _seen = _seen max seen
      }
      if (messages.nonEmpty) Progress.Data.update_agent(db, _agent_uuid, _seen)

      body
    }
  }

  def sync(): Unit = sync_database {}

  private def output_database(message: Progress.Message, body: => Unit): Unit =
    sync_database {
      val serial = Progress.Data.next_messages_serial(db, _context)
      Progress.Data.write_messages(db, _context, serial, message)

      body

      _seen = _seen max serial
      Progress.Data.update_agent(db, _agent_uuid, _seen)
    }

  override def output(message: Progress.Message): Unit =
    output_database(message, if (do_output(message)) base_progress.output(message))

  override def theory(theory: Progress.Theory): Unit =
    output_database(theory.message, base_progress.theory(theory))

  override def nodes_status(nodes_status: Document_Status.Nodes_Status): Unit =
    base_progress.nodes_status(nodes_status)

  override def verbose: Boolean = base_progress.verbose

  override def stop(): Unit = synchronized { base_progress.stop(); sync() }
  override def stopped: Boolean = sync_database { base_progress.stopped }

  override def toString: String = super.toString + ": database " + db

  init()
  sync()
}


/* structured program progress */

object Program_Progress {
  class Program private[Program_Progress](heading: String, title: String) {
    private val output_buffer = new StringBuffer(256)  // synchronized

    def output(message: Progress.Message): Unit = synchronized {
      if (output_buffer.length() > 0) output_buffer.append('\n')
      output_buffer.append(message.output_text)
    }

    val start_time: Time = Time.now()
    private var stop_time: Option[Time] = None
    def stop_now(): Unit = synchronized { stop_time = Some(Time.now()) }

    def output(): (Command.Results, XML.Body) = synchronized {
      val output_text = output_buffer.toString
      val elapsed_time = stop_time.map(t => t - start_time)

      val message_prefix = heading + " "
      val message_suffix =
        elapsed_time match {
          case None => " ..."
          case Some(t) => " ... (" + t.message + " elapsed time)"
        }

      val (results, message) =
        if (output_text.isEmpty) {
          (Command.Results.empty, XML.string(message_prefix + title + message_suffix))
        }
        else {
          val i = Document_ID.make()
          val results = Command.Results.make(List(i -> Protocol.writeln_message(output_text)))
          val message =
            XML.string(message_prefix) :::
            List(XML.Elem(Markup(Markup.WRITELN, Markup.Serial(i)), XML.string(title))) :::
            XML.string(message_suffix)
          (results, message)
        }

      (results, List(XML.elem(Markup.TRACING_MESSAGE, message)))
    }
  }
}

abstract class Program_Progress(
  default_heading: String = "Running",
  default_title: String = "program",
  override val verbose: Boolean = false
) extends Progress {
  private var _finished_programs: List[Program_Progress.Program] = Nil
  private var _running_program: Option[Program_Progress.Program] = None

  def output(): (Command.Results, XML.Body) = synchronized {
    val programs = (_running_program.toList ::: _finished_programs).reverse
    val programs_output = programs.map(_.output())
    val results = Command.Results.merge(programs_output.map(_._1))
    val body = Library.separate(Pretty.Separator, programs_output.map(_._2)).flatten
    (results, body)
  }

  private def start_program(heading: String, title: String): Unit = synchronized {
    _running_program = Some(new Program_Progress.Program(heading, title))
  }

  def stop_program(): Unit = synchronized {
    _running_program match {
      case Some(program) =>
        program.stop_now()
        _finished_programs ::= program
        _running_program = None
      case None =>
    }
  }

  def detect_program(s: String): Option[String]

  override def output(message: Progress.Message): Unit = synchronized {
    val writeln_msg = if (message.kind == Progress.Kind.writeln) message.text else ""
    detect_program(writeln_msg).map(Word.explode) match {
      case Some(a :: bs) =>
        stop_program()
        start_program(a, Word.implode(bs))
      case _ =>
        if (_running_program.isEmpty) start_program(default_heading, default_title)
        if (do_output(message)) _running_program.get.output(message)
    }
  }
}
