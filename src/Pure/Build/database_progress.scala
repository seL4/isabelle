/*  Title:      Pure/Build/database_progress.scala
    Author:     Makarius

System progress backed by shared database: local SQLite or remote PostgreSQL.
*/

package isabelle


import scala.collection.immutable.SortedMap


object Database_Progress {
  /* SQL data model */

  object private_data extends SQL.Data("isabelle_progress") {
    val database: Path = Path.explode("$ISABELLE_HOME_USER/progress.db")

    override lazy val tables: SQL.Tables =
      SQL.Tables(Base.table, Agents.table, Messages.table)

    object Base {
      val context_uuid = SQL.Column.string("context_uuid").make_primary_key
      val context = SQL.Column.long("context").make_primary_key
      val stopped = SQL.Column.bool("stopped")

      val table = make_table(List(context_uuid, context, stopped))
    }

    object Agents {
      val agent_uuid = SQL.Column.string("agent_uuid").make_primary_key
      val context_uuid = SQL.Column.string("context_uuid").make_primary_key
      val kind = SQL.Column.string("kind")
      val hostname = SQL.Column.string("hostname")
      val java_pid = SQL.Column.long("java_pid")
      val java_start = SQL.Column.date("java_start")
      val start = SQL.Column.date("start")
      val stamp = SQL.Column.date("stamp")
      val stop = SQL.Column.date("stop")
      val seen = SQL.Column.long("seen")

      val table =
        make_table(
          List(agent_uuid, context_uuid, kind, hostname, java_pid, java_start,
            start, stamp, stop, seen),
          name = "agents")
    }

    object Messages {
      type T = SortedMap[Long, Progress.Message]
      val empty: T = SortedMap.empty

      val context = SQL.Column.long("context").make_primary_key
      val serial = SQL.Column.long("serial").make_primary_key
      val kind = SQL.Column.int("kind")
      val text = SQL.Column.string("text")
      val verbose = SQL.Column.bool("verbose")

      val table = make_table(List(context, serial, kind, text, verbose), name = "messages")
    }

    val channel: String = Base.table.name
    val channel_ping: SQL.Notification = SQL.Notification(channel, payload = "ping")
    val channel_output: SQL.Notification = SQL.Notification(channel, payload = "output")

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
      stop_now: Boolean = false
    ): Unit = {
      val sql = Agents.agent_uuid.where_equal(agent_uuid)

      val stop =
        db.execute_query_statementO(
          Agents.table.select(List(Agents.stop), sql = sql), _.get_date(Agents.stop)).flatten

      db.execute_statement(
        Agents.table.update(List(Agents.stamp, Agents.stop, Agents.seen), sql = sql),
        body = { stmt =>
          val now = db.now()
          stmt.date(1) = now
          stmt.date(2) = if (stop_now) Some(now) else stop
          stmt.long(3) = seen
        })
    }

    def read_messages_serial(db: SQL.Database, context: Long): Long =
      db.execute_query_statementO(
        Messages.table.select(
          List(Messages.serial.max), sql = Base.context.where_equal(context)),
        _.long(Messages.serial)
      ).getOrElse(0L)

    def read_messages(db: SQL.Database, context: Long, seen: Long = 0): Messages.T =
      db.execute_query_statement(
        Messages.table.select(
          List(Messages.serial, Messages.kind, Messages.text, Messages.verbose),
          sql =
            SQL.where_and(
              Messages.context.ident + " = " + context,
              if (seen <= 0) "" else Messages.serial.ident + " > " + seen)),
        SortedMap.from[Long, Progress.Message],
        { res =>
          val serial = res.long(Messages.serial)
          val kind = Progress.Kind.fromOrdinal(res.int(Messages.kind))
          val text = res.string(Messages.text)
          val verbose = res.bool(Messages.verbose)
          serial -> Progress.Message(kind, text, verbose = verbose)
        }
      )

    def write_messages(
      db: SQL.Database,
      context: Long,
      messages: List[(Long, Progress.Message)]
    ): Unit = {
      db.execute_batch_statement(Messages.table.insert(), batch =
        for ((serial, message) <- messages) yield { (stmt: SQL.Statement) =>
          stmt.long(1) = context
          stmt.long(2) = serial
          stmt.int(3) = message.kind.ordinal
          stmt.string(4) = message.text
          stmt.bool(5) = message.verbose
        })
    }
  }
}

class Database_Progress(
  db: SQL.Database,
  base_progress: Progress,
  input_messages: Boolean = false,
  kind: String = "progress",
  hostname: String = Isabelle_System.hostname(),
  context_uuid: String = UUID.random_string(),
  timeout: Option[Time] = None,
  tick_expire: Int = 50)
extends Progress {
  database_progress =>

  override def now(): Date = db.now()
  override val start: Date = now()

  if (UUID.unapply(context_uuid).isEmpty) {
    error("Bad Database_Progress.context_uuid: " + quote(context_uuid))
  }

  private var _tick: Long = 0
  private var _agent_uuid: String = ""
  private var _context: Long = -1
  private var _serial: Long = 0
  private var _consumer: Consumer_Thread[Progress.Output] = null

  def agent_uuid: String = synchronized { _agent_uuid }

  private def init(): Unit = synchronized {
    db.listen(Database_Progress.private_data.channel)
    Database_Progress.private_data.transaction_lock(db,
      create = true,
      label = "Database_Progress.init"
    ) {
      Database_Progress.private_data.read_progress_context(db, context_uuid) match {
        case Some(context) =>
          _context = context
          _agent_uuid = UUID.random_string()
        case None =>
          _context = Database_Progress.private_data.next_progress_context(db)
          _agent_uuid = context_uuid
          db.execute_statement(Database_Progress.private_data.Base.table.insert(), { stmt =>
            stmt.string(1) = context_uuid
            stmt.long(2) = _context
            stmt.bool(3) = false
          })
      }
      db.execute_statement(Database_Progress.private_data.Agents.table.insert(), { stmt =>
        val java = ProcessHandle.current()
        val java_pid = java.pid
        val java_start = Date.instant(java.info.startInstant.get)

        stmt.string(1) = _agent_uuid
        stmt.string(2) = context_uuid
        stmt.string(3) = kind
        stmt.string(4) = hostname
        stmt.long(5) = java_pid
        stmt.date(6) = java_start
        stmt.date(7) = start
        stmt.date(8) = start
        stmt.date(9) = None
        stmt.long(10) = 0L
      })
    }
    if (context_uuid == _agent_uuid) db.vacuum(Database_Progress.private_data.tables.list)

    def consume(bulk_output: List[Progress.Output]): List[Exn.Result[Unit]] = {
      val expired = synchronized { _tick += 1; _tick % tick_expire == 0 }
      val received = db.receive(n => n.channel == Database_Progress.private_data.channel)
      val ok =
        bulk_output.nonEmpty || expired || base_progress.stopped ||
        received.isEmpty ||
        received.get.contains(Database_Progress.private_data.channel_ping) ||
        input_messages && received.get.contains(Database_Progress.private_data.channel_output)
      if (ok) {
        sync_database {
          if (bulk_output.nonEmpty) {
            for (out <- bulk_output) {
              out match {
                case message: Progress.Message =>
                  if (do_output(message)) base_progress.output(message)
                case theory: Progress.Theory => base_progress.theory(theory)
              }
            }

            val messages =
              for ((out, i) <- bulk_output.zipWithIndex)
                yield (_serial + i + 1) -> out.message

            Database_Progress.private_data.write_messages(db, _context, messages)
            _serial = messages.last._1

            db.send(Database_Progress.private_data.channel_output)
          }
          bulk_output.map(_ => Exn.Res(()))
        }
      }
      else Nil
    }

    _consumer = Consumer_Thread.fork_bulk[Progress.Output](name = "Database_Progress.consumer")(
      bulk = _ => true,
      timeout = timeout,
      consume = { bulk_output =>
        val results =
          if (bulk_output.isEmpty) consume(Nil)
          else bulk_output.grouped(200).toList.flatMap(consume)
        (results, true) })
  }

  def close(): Unit = synchronized {
    if (_context > 0) {
      _consumer.shutdown()
      _consumer = null

      Database_Progress.private_data.transaction_lock(db, label = "Database_Progress.exit") {
        Database_Progress.private_data.update_agent(db, _agent_uuid, _serial, stop_now = true)
      }
      _context = 0
    }
    db.close()
  }

  private def sync_context[A](body: => A): A = synchronized {
    if (_context < 0) throw new IllegalStateException("Database_Progress before init")
    if (_context == 0) throw new IllegalStateException("Database_Progress after exit")

    body
  }

  private def sync_database[A](body: => A): A = synchronized {
    Database_Progress.private_data.transaction_lock(db, label = "Database_Progress.sync_database") {
      val stopped_db = Database_Progress.private_data.read_progress_stopped(db, _context)

      if (stopped_db && !base_progress.stopped) base_progress.stop()
      if (!stopped_db && base_progress.stopped) {
        Database_Progress.private_data.write_progress_stopped(db, _context, true)
        db.send(Database_Progress.private_data.channel_ping)
      }

      val serial0 = _serial
      if (input_messages) {
        val messages = Database_Progress.private_data.read_messages(db, _context, seen = _serial)
        for ((message_serial, message) <- messages) {
          if (base_progress.do_output(message)) base_progress.output(message)
          _serial = _serial max message_serial
        }
      }
      else {
        _serial = _serial max Database_Progress.private_data.read_messages_serial(db, _context)
      }

      val res = body

      if (_serial != serial0) Database_Progress.private_data.update_agent(db, _agent_uuid, _serial)

      res
    }
  }

  private def sync(): Unit = sync_database {}

  override def output(message: Progress.Message): Unit = sync_context { _consumer.send(message) }
  override def theory(theory: Progress.Theory): Unit = sync_context { _consumer.send(theory) }

  override def nodes_status(
    domain: List[Document.Node.Name],
    nodes_status: Document_Status.Nodes_Status
  ): Unit = base_progress.nodes_status(domain, nodes_status)

  override def verbose: Boolean = base_progress.verbose

  override def stop(): Unit = sync_context { base_progress.stop(); sync() }
  override def stopped: Boolean = sync_context { base_progress.stopped }

  override def toString: String = super.toString + ": database " + db

  init()
  sync()
}
