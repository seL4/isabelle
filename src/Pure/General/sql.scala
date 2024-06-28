/*  Title:      Pure/General/sql.scala
    Author:     Makarius

Support for SQL databases: SQLite and PostgreSQL.

See https://docs.oracle.com/en/java/javase/21/docs/api/java.sql/java/sql/Connection.html
*/

package isabelle


import java.time.OffsetDateTime
import java.sql.{DriverManager, Connection, PreparedStatement, ResultSet, SQLException}

import org.sqlite.SQLiteConfig
import org.sqlite.jdbc4.JDBC4Connection
import org.postgresql.PGConnection

import scala.collection.mutable


object SQL {
  lazy val time_start = Time.now()

  /** SQL language **/

  type Source = String


  /* concrete syntax */

  def string(s: String): Source =
    Library.string_builder(hint = s.length + 10) { result =>
      val q = '\''
      result += q
      for (c <- s.iterator) {
        if (c == '\u0000') error("Illegal NUL character in SQL string literal")
        if (c == q) result += q
        result += c
      }
      result += q
    }

  def ident(s: String): Source =
    Long_Name.implode(Long_Name.explode(s).map(a => quote(a.replace("\"", "\"\""))))

  def enclose(s: Source): Source = "(" + s + ")"
  def enclosure(ss: Iterable[Source]): Source = ss.mkString("(", ", ", ")")

  def separate(sql: Source): Source =
    if_proper(sql.nonEmpty && sql(0) != ' ', " ") + sql

  def select(columns: List[Column] = Nil, distinct: Boolean = false, sql: Source = ""): Source =
    "SELECT " + if_proper(distinct, "DISTINCT ") +
    (if (columns.isEmpty) "*" else commas(columns.map(_.ident))) + " FROM " + sql

  val join_outer: Source = " LEFT OUTER JOIN "
  val join_inner: Source = " INNER JOIN "

  def MULTI(args: Iterable[Source]): Source =
    args.iterator.filter(_.nonEmpty).mkString(";\n")
  def multi(args: Source*): Source = MULTI(args)

  def infix(op: Source, args: Iterable[Source]): Source = {
    val body = args.iterator.filter(_.nonEmpty).mkString(" " + op + " ")
    if_proper(body, enclose(body))
  }

  def AND(args: Iterable[Source]): Source = infix("AND", args)
  def OR(args: Iterable[Source]): Source = infix("OR", args)

  def and(args: Source*): Source = AND(args)
  def or(args: Source*): Source = OR(args)

  val TRUE: Source = "TRUE"
  val FALSE: Source = "FALSE"

  def equal(sql: Source, x: Int): Source = sql + " = " + x
  def equal(sql: Source, x: Long): Source = sql + " = " + x
  def equal(sql: Source, x: String): Source = sql + " = " + string(x)

  def member_int(sql: Source, set: Iterable[Int]): Source =
    if (set.isEmpty) FALSE else OR(set.iterator.map(equal(sql, _)).toList)
  def member_long(sql: Source, set: Iterable[Long]): Source =
    if (set.isEmpty) FALSE else OR(set.iterator.map(equal(sql, _)).toList)
  def member(sql: Source, set: Iterable[String]): Source =
    if (set.isEmpty) FALSE else OR(set.iterator.map(equal(sql, _)).toList)

  def where(sql: Source): Source = if_proper(sql, " WHERE " + sql)
  def where_and(args: Source*): Source = where(and(args:_*))
  def where_or(args: Source*): Source = where(or(args:_*))


  /* types */

  enum Type { case Boolean, Int, Long, Double, String, Bytes, Date }

  val sql_type_postgresql: Type => Source =
    {
      case Type.Boolean => "BOOLEAN"
      case Type.Int => "INTEGER"
      case Type.Long => "BIGINT"
      case Type.Double => "DOUBLE PRECISION"
      case Type.String => "TEXT"
      case Type.Bytes => "BYTEA"
      case Type.Date => "TIMESTAMP WITH TIME ZONE"
    }

  val sql_type_sqlite: Type => Source =
    {
      case Type.Boolean => "INTEGER"
      case Type.Bytes => "BLOB"
      case Type.Date => "TEXT"
      case t => sql_type_postgresql(t)
    }


  /* columns */

  object Column {
    def bool(name: String, strict: Boolean = false, primary_key: Boolean = false): Column =
      Column(name, Type.Boolean, strict, primary_key)
    def int(name: String, strict: Boolean = false, primary_key: Boolean = false): Column =
      Column(name, Type.Int, strict, primary_key)
    def long(name: String, strict: Boolean = false, primary_key: Boolean = false): Column =
      Column(name, Type.Long, strict, primary_key)
    def double(name: String, strict: Boolean = false, primary_key: Boolean = false): Column =
      Column(name, Type.Double, strict, primary_key)
    def string(name: String, strict: Boolean = false, primary_key: Boolean = false): Column =
      Column(name, Type.String, strict, primary_key)
    def bytes(name: String, strict: Boolean = false, primary_key: Boolean = false): Column =
      Column(name, Type.Bytes, strict, primary_key)
    def date(name: String, strict: Boolean = false, primary_key: Boolean = false): Column =
      Column(name, Type.Date, strict, primary_key)
  }

  sealed case class Column(
    name: String,
    T: Type,
    strict: Boolean = false,
    primary_key: Boolean = false,
    expr: SQL.Source = ""
  ) {
    def equals_name(other: Column): Boolean = name == other.name

    def make_primary_key: Column = copy(primary_key = true)

    def apply(table: Table): Column =
      Column(Long_Name.qualify(table.name, name), T, strict = strict, primary_key = primary_key)

    def ident: Source =
      if_proper(expr, enclose(expr) + " AS ") + SQL.ident(name)

    def decl(sql_type: Type => Source): Source =
      ident + " " + sql_type(T) + if_proper(strict || primary_key, " NOT NULL")

    def defined: String = ident + " IS NOT NULL"
    def undefined: String = ident + " IS NULL"

    def equal(x: Int): Source = SQL.equal(ident, x)
    def equal(x: Long): Source = SQL.equal(ident, x)
    def equal(x: String): Source = SQL.equal(ident, x)

    def where_equal(x: Int): Source = SQL.where(equal(x))
    def where_equal(x: Long): Source = SQL.where(equal(x))
    def where_equal(x: String): Source = SQL.where(equal(x))

    def member_int(set: Iterable[Int]): Source = SQL.member_int(ident, set)
    def member_long(set: Iterable[Long]): Source = SQL.member_long(ident, set)
    def member(set: Iterable[String]): Source = SQL.member(ident, set)

    def where_member_int(set: Iterable[Int]): Source = SQL.where(member_int(set))
    def where_member_long(set: Iterable[Long]): Source = SQL.where(member_long(set))
    def where_member(set: Iterable[String]): Source = SQL.where(member(set))

    def make_expr(e: SQL.Source): Column = copy(expr = e)
    def max: Column = make_expr("MAX(" + ident + ")")

    override def toString: Source = ident
  }

  def order_by(columns: List[Column], descending: Boolean = false): Source =
    " ORDER BY " + columns.mkString(", ") + if_proper(descending, " DESC")


  /* tables */

  sealed case class Table(name: String, columns: List[Column], body: Source = "") {
    Library.duplicates(columns.map(_.name)) match {
      case Nil =>
      case bad => error("Duplicate column names " + commas_quote(bad) + " for table " + quote(name))
    }

    def ident: Source = SQL.ident(name)

    def query: Source =
      if (body == "") error("Missing SQL body for table " + quote(name))
      else SQL.enclose(body)

    def query_named: Source = query + " AS " + SQL.ident(name)

    def create(sql_type: Type => Source): Source = {
      val primary_key =
        columns.filter(_.primary_key).map(_.name) match {
          case Nil => Nil
          case keys => List("PRIMARY KEY " + enclosure(keys))
        }
      "CREATE TABLE " + ident + " " + enclosure(columns.map(_.decl(sql_type)) ::: primary_key)
    }

    def insert_cmd(cmd: Source = "INSERT", sql: Source = ""): Source =
      cmd + " INTO " + ident + " VALUES " + enclosure(columns.map(_ => "?")) + SQL.separate(sql)

    def insert(sql: Source = ""): Source = insert_cmd(sql = sql)

    def delete(sql: Source = ""): Source =
      "DELETE FROM " + ident + SQL.separate(sql)

    def update(update_columns: List[Column] = Nil, sql: Source = ""): Source =
      "UPDATE " + ident + " SET " + commas(update_columns.map(c => c.ident + " = ?")) +
        SQL.separate(sql)

    def select(
      select_columns: List[Column] = Nil,
      distinct: Boolean = false,
      sql: Source = ""
    ): Source = SQL.select(select_columns, distinct = distinct, sql = ident + SQL.separate(sql))

    override def toString: Source = ident
  }


  /* table groups */

  object Tables {
    def list(list: List[Table]): Tables = new Tables(list)
    def apply(args: Table*): Tables = list(args.toList)
  }

  final class Tables private(val list: List[Table]) extends Iterable[Table] {
    override def toString: String = list.mkString("SQL.Tables(", ", ", ")")

    def iterator: Iterator[Table] = list.iterator

    def index(table: Table): Int =
      iterator.zipWithIndex
        .collectFirst({ case (t, i) if t.name == table.name => i })
        .getOrElse(error("No table " + quote(table.name)))

    // requires transaction
    def lock(db: Database, create: Boolean = false): Boolean = {
      if (create) foreach(db.create_table(_))
      val sql = db.lock_tables(list)
      if (sql.nonEmpty) { db.execute_statement(sql); true }
      else false
    }
  }


  /* access data */

  def transaction_logger(): Logger =
    new System_Logger(guard_time = Time.guard_property("isabelle.transaction_trace"))

  abstract class Data(table_prefix: String = "") {
    def tables: Tables

    def transaction_lock[A](
      db: Database,
      create: Boolean = false,
      label: String = "",
      log: Logger = transaction_logger()
    )(body: => A): A = {
      db.transaction_lock(tables, create = create, label = label, log = log)(body)
    }

    def make_table(columns: List[Column], body: String = "", name: String = ""): Table = {
      val table_name =
        List(proper_string(table_prefix), proper_string(name)).flatten.mkString("_")
      require(table_name.nonEmpty, "Undefined database table name")
      Table(table_name, columns, body = body)
    }
  }



  /** SQL database operations **/

  /* statements */

  class Batch_Error(val results: List[Int]) extends SQLException

  class Statement private[SQL](val db: Database, val rep: PreparedStatement) extends AutoCloseable {
    stmt =>

    object bool {
      def update(i: Int, x: Boolean): Unit = rep.setBoolean(i, x)
      def update(i: Int, x: Option[Boolean]): Unit = {
        if (x.isDefined) update(i, x.get)
        else rep.setNull(i, java.sql.Types.BOOLEAN)
      }
    }
    object int {
      def update(i: Int, x: Int): Unit = rep.setInt(i, x)
      def update(i: Int, x: Option[Int]): Unit = {
        if (x.isDefined) update(i, x.get)
        else rep.setNull(i, java.sql.Types.INTEGER)
      }
    }
    object long {
      def update(i: Int, x: Long): Unit = rep.setLong(i, x)
      def update(i: Int, x: Option[Long]): Unit = {
        if (x.isDefined) update(i, x.get)
        else rep.setNull(i, java.sql.Types.BIGINT)
      }
    }
    object double {
      def update(i: Int, x: Double): Unit = rep.setDouble(i, x)
      def update(i: Int, x: Option[Double]): Unit = {
        if (x.isDefined) update(i, x.get)
        else rep.setNull(i, java.sql.Types.DOUBLE)
      }
    }
    object string {
      def update(i: Int, x: String): Unit = rep.setString(i, x)
      def update(i: Int, x: Option[String]): Unit = update(i, x.orNull)
    }
    object bytes {
      def update(i: Int, bytes: Bytes): Unit = {
        if (bytes == null) rep.setBytes(i, null)
        else if (bytes.size > Int.MaxValue) throw new IllegalArgumentException
        else rep.setBinaryStream(i, bytes.stream(), bytes.size.toInt)
      }
      def update(i: Int, bytes: Option[Bytes]): Unit = update(i, bytes.orNull)
    }
    object date {
      def update(i: Int, date: Date): Unit = db.update_date(stmt, i, date)
      def update(i: Int, date: Option[Date]): Unit = update(i, date.orNull)
    }

    def execute(): Boolean = rep.execute()

    def execute_batch(batch: IterableOnce[Statement => Unit]): Unit = {
      val it = batch.iterator
      if (it.nonEmpty) {
        for (body <- it) { body(this); rep.addBatch() }
        val res = rep.executeBatch()
        if (!res.forall(i => i >= 0 || i == java.sql.Statement.SUCCESS_NO_INFO)) {
          throw new Batch_Error(res.toList)
        }
      }
    }

    def execute_query(): Result = new Result(this, rep.executeQuery())

    override def close(): Unit = rep.close()
  }


  /* results */

  class Result private[SQL](val stmt: Statement, val rep: ResultSet) extends AutoCloseable {
    res =>

    def next(): Boolean = rep.next()

    def iterator[A](get: Result => A): Iterator[A] = new Iterator[A] {
      private var _next: Boolean = res.next()
      def hasNext: Boolean = _next
      def next(): A = { val x = get(res); _next = res.next(); x }
    }

    def bool(column: Column): Boolean = rep.getBoolean(column.name)
    def int(column: Column): Int = rep.getInt(column.name)
    def long(column: Column): Long = rep.getLong(column.name)
    def double(column: Column): Double = rep.getDouble(column.name)
    def string(column: Column): String = {
      val s = rep.getString(column.name)
      if (s == null) "" else s
    }
    def bytes(column: Column): Bytes = {
      val bs = rep.getBytes(column.name)
      if (bs == null) Bytes.empty else Bytes(bs)
    }
    def date(column: Column): Date = stmt.db.date(res, column)

    def timing(c1: Column, c2: Column, c3: Column): Timing =
      Timing(Time.ms(long(c1)), Time.ms(long(c2)), Time.ms(long(c3)))

    def get[A](column: Column, f: Column => A): Option[A] = {
      val x = f(column)
      if (rep.wasNull || x == null) None else Some(x)
    }
    def get_bool(column: Column): Option[Boolean] = get(column, bool)
    def get_int(column: Column): Option[Int] = get(column, int)
    def get_long(column: Column): Option[Long] = get(column, long)
    def get_double(column: Column): Option[Double] = get(column, double)
    def get_string(column: Column): Option[String] = get(column, string)
    def get_bytes(column: Column): Option[Bytes] = get(column, bytes)
    def get_date(column: Column): Option[Date] = get(column, date)

    override def close(): Unit = rep.close()
  }


  /* notifications: IPC via database server */

  sealed case class Notification(channel: String, payload: String = "") {
    override def toString: String =
      "Notification(" + channel + if_proper(payload, "," + payload) + ")"
  }


  /* database */

  trait Database extends AutoCloseable {
    db =>

    def is_sqlite: Boolean = isInstanceOf[SQLite.Database]
    def is_postgresql: Boolean = isInstanceOf[PostgreSQL.Database]

    def vacuum(tables: List[SQL.Table] = Nil): Unit =
      if (is_sqlite) execute_statement("VACUUM")  // always FULL
      else if (tables.isEmpty) execute_statement("VACUUM FULL")
      else if (postgresql_major_version.get <= 10) {
        for (t <- tables) execute_statement("VACUUM " + t.ident)
      }
      else execute_statement("VACUUM" + commas(tables.map(_.ident)))

    def now(): Date


    /* types */

    def sql_type(T: Type): Source


    /* connection */

    def connection: Connection

    def sqlite_connection: Option[JDBC4Connection] =
      connection match { case conn: JDBC4Connection => Some(conn) case _ => None }

    def postgresql_connection: Option[PGConnection] =
      connection match { case conn: PGConnection => Some(conn) case _ => None }

    def the_sqlite_connection: JDBC4Connection =
      sqlite_connection getOrElse
        error("SQLite connection expected, but found " + connection.getClass.getName)

    def the_postgresql_connection: PGConnection =
      postgresql_connection getOrElse
        error("PostgreSQL connection expected, but found " + connection.getClass.getName)

    def postgresql_major_version: Option[Int] =
      if (is_postgresql) {
        def err(s: String): Nothing = error("Bad PostgreSQL version " + s)

        the_postgresql_connection.getParameterStatus("server_version") match {
          case null => err("null")
          case str =>
            str.iterator.takeWhile(Symbol.is_ascii_digit).mkString match {
              case Value.Int(m) => Some(m)
              case _ => err(quote(str))
            }
        }
      }
      else None

    override def close(): Unit = connection.close()

    def transaction[A](body: => A): A = connection.synchronized {
      require(connection.getAutoCommit(), "transaction already active")
      try {
        connection.setAutoCommit(false)
        try {
          val result = body
          connection.commit()
          result
        }
        catch { case exn: Throwable => connection.rollback(); throw exn }
      }
      finally { connection.setAutoCommit(true) }
    }

    def transaction_lock[A](
      tables: Tables,
      create: Boolean = false,
      label: String = "",
      log: Logger = transaction_logger()
    )(body: => A): A = {
      val trace_count = - SQL.transaction_count()
      val trace_start = Time.now()
      var trace_nl = false

      def trace(msg: String): Unit = {
        val trace_time = Time.now() - trace_start
        if (log.guard(trace_time)) {
          time_start
          val nl =
            if (trace_nl) ""
            else { trace_nl = true; "\nnow = " + (Time.now() - time_start).toString + "\n" }
          log(nl + trace_time + " transaction " + trace_count +
            if_proper(label, " " + label) + ": " + msg)
        }
      }

      try {
        val res =
          transaction {
            trace("begin")
            if (tables.lock(db, create = create)) {
              trace("locked " + commas_quote(tables.list.map(_.name)))
            }
            val res = Exn.capture { body }
            trace("end")
            res
          }
        trace("commit")
        Exn.release(res)
      }
      catch { case exn: Throwable => trace("crash"); throw exn }
    }

    def lock_tables(tables: List[Table]): Source = ""  // PostgreSQL only


    /* statements and results */

    def statement(sql: Source): Statement =
      new Statement(db, connection.prepareStatement(sql))

    def using_statement[A](sql: Source)(f: Statement => A): A =
      using(statement(sql))(f)

    def execute_statement(sql: Source, body: Statement => Unit = _ => ()): Unit =
      using_statement(sql) { stmt => body(stmt); stmt.execute() }

    def execute_batch_statement(
      sql: Source,
      batch: IterableOnce[Statement => Unit] = Nil
    ): Unit = using_statement(sql) { stmt => stmt.execute_batch(batch) }

    def execute_query_statement[A, B](
      sql: Source,
      make_result: Iterator[A] => B,
      get: Result => A
    ): B = {
      using_statement(sql) { stmt =>
        using(stmt.execute_query()) { res => make_result(res.iterator(get)) }
      }
    }

    def execute_query_statementO[A](sql: Source, get: Result => A): Option[A] =
      execute_query_statement[A, Option[A]](sql, _.nextOption, get)

    def execute_query_statementB(sql: Source): Boolean =
      using_statement(sql)(stmt => using(stmt.execute_query())(_.next()))

    def update_date(stmt: Statement, i: Int, date: Date): Unit
    def date(res: Result, column: Column): Date

    def insert_permissive(table: Table, sql: Source = ""): Source

    def destroy(table: Table): Source = "DROP TABLE IF EXISTS " + table


    /* tables and views */

    def name_pattern(name: String): String = {
      val escape = connection.getMetaData.getSearchStringEscape
      name.iterator.map(c =>
        if_proper(c == '_' || c == '%' || c == escape(0), escape) + c).mkString
    }

    def get_tables(pattern: String = "%"): List[String] = {
      val result = new mutable.ListBuffer[String]
      val rs = connection.getMetaData.getTables(null, null, pattern, null)
      while (rs.next) { result += rs.getString(3) }
      result.toList
    }

    def get_table_columns(
      table_pattern: String = "%",
      pattern: String = "%"
    ): List[(String, String)] = {
      val result = new mutable.ListBuffer[(String, String)]
      val rs = connection.getMetaData.getColumns(null, null, table_pattern, pattern)
      while (rs.next) { result += (rs.getString(3) -> rs.getString(4)) }
      result.toList
    }

    def exists_table(name: String): Boolean =
      get_tables(pattern = name_pattern(name)).nonEmpty

    def exists_table(table: Table): Boolean = exists_table(table.name)

    def exists_table_column(table_name: String, name: String): Boolean =
      get_table_columns(table_pattern = name_pattern(table_name), pattern = name_pattern(name))
        .nonEmpty

    def exists_table_column(table: Table, column: Column): Boolean =
      exists_table_column(table.name, column.name)

    def create_table(table: Table, sql: Source = ""): Unit = {
      if (!exists_table(table)) {
        execute_statement(table.create(sql_type) + SQL.separate(sql))
        if (is_postgresql) {
          for (column <- table.columns if column.T == SQL.Type.Bytes) {
            execute_statement(
              "ALTER TABLE " + table + " ALTER COLUMN " + column + " SET STORAGE EXTERNAL")
          }
        }
      }
    }

    def create_view(table: Table): Unit = {
      if (!exists_table(table)) {
        execute_statement("CREATE VIEW " + table + " AS " + { table.query; table.body })
      }
    }


    /* notifications (PostgreSQL only) */

    def listen(channel: String): Unit = ()
    def unlisten(channel: String = "*"): Unit = ()
    def send(channel: String, payload: String): Unit = ()
    final def send(channel: String): Unit = send(channel, "")
    final def send(notification: Notification): Unit =
      send(notification.channel, notification.payload)
    def receive(filter: Notification => Boolean): Option[List[Notification]] = None
  }


  private val transaction_count = Counter.make()
}



/** SQLite **/

object SQLite {
  // see https://www.sqlite.org/lang_datefunc.html
  val date_format: Date.Format = Date.Format("uuuu-MM-dd HH:mm:ss.SSS x")

  lazy val init_jdbc: Unit = {
    val lib_path = Path.explode("$ISABELLE_SQLITE_HOME/" + Platform.jvm_platform)
    val lib_name = File.get_file(lib_path).file_name

    System.setProperty("org.sqlite.lib.path", File.platform_path(lib_path))
    System.setProperty("org.sqlite.lib.name", lib_name)

    Class.forName("org.sqlite.JDBC")
  }

  def open_database(path: Path, restrict: Boolean = false): Database = {
    init_jdbc
    val path0 = path.expand
    val s0 = File.platform_path(path0)
    val s1 = if (Platform.is_windows) s0.replace('\\', '/') else s0

    val config = new SQLiteConfig()
    config.setEncoding(SQLiteConfig.Encoding.UTF8)
    val connection = config.createConnection("jdbc:sqlite:" + s1)

    val db = new Database(path0.toString, connection)

    try { if (restrict) File.restrict(path0) }
    catch { case exn: Throwable => db.close(); throw exn }

    db
  }

  class Database private[SQLite](name: String, val connection: Connection) extends SQL.Database {
    override def toString: String = name

    override def now(): Date = Date.now()

    def sql_type(T: SQL.Type): SQL.Source = SQL.sql_type_sqlite(T)

    def update_date(stmt: SQL.Statement, i: Int, date: Date): Unit =
      if (date == null) stmt.string(i) = (null: String)
      else stmt.string(i) = date_format(date)

    def date(res: SQL.Result, column: SQL.Column): Date =
      proper_string(res.string(column)) match {
        case None => null
        case Some(s) => date_format.parse(s)
      }

    def insert_permissive(table: SQL.Table, sql: SQL.Source = ""): SQL.Source =
      table.insert_cmd(cmd = "INSERT OR IGNORE", sql = sql)
  }
}



/** PostgreSQL **/

// see https://www.postgresql.org/docs/14/index.html
// see https://jdbc.postgresql.org/documentation

object PostgreSQL {
  type Source = SQL.Source

  lazy val init_jdbc: Unit = Class.forName("org.postgresql.Driver")

  val default_server: SSH.Server = SSH.local_server(port = 5432)

  def open_database(
    user: String,
    password: String,
    database: String = "",
    server: SSH.Server = default_server,
    server_close: Boolean = false,
    receiver_delay: Time = Time.seconds(0.5)
  ): Database = {
    init_jdbc

    if (user.isEmpty) error("Undefined database user")
    if (server.host.isEmpty) error("Undefined database server host")
    if (server.port <= 0) error("Undefined database server port")

    val name = proper_string(database) getOrElse user
    val url = "jdbc:postgresql://" + server.host + ":" + server.port + "/" + name
    val ssh = server.ssh_system.ssh_session
    val print =
      "server " + quote(user + "@" + server + "/" + name) +
        if_proper(ssh, " via ssh " + quote(ssh.get.toString))

    val connection = DriverManager.getConnection(url, user, password)
    val db = new Database(connection, print, server, server_close, receiver_delay)

    try { db.execute_statement("SET standard_conforming_strings = on") }
    catch { case exn: Throwable => db.close(); throw exn }

    db
  }

  def open_server(
    options: Options,
    host: String = "",
    port: Int = 0,
    ssh_host: String = "",
    ssh_port: Int = 0,
    ssh_user: String = ""
  ): SSH.Server = {
    val server_host = proper_string(host).getOrElse(default_server.host)
    val server_port = if (port > 0) port else default_server.port

    if (ssh_host.isEmpty) SSH.local_server(host = server_host, port = server_port)
    else {
      SSH.open_server(options, host = ssh_host, port = ssh_port, user = ssh_user,
        remote_host = server_host, remote_port = server_port)
    }
  }

  def open_database_server(
    options: Options,
    user: String = "",
    password: String = "",
    database: String = "",
    server: SSH.Server = SSH.no_server,
    host: String = "",
    port: Int = 0,
    ssh_host: String = "",
    ssh_port: Int = 0,
    ssh_user: String = ""
  ): PostgreSQL.Database = {
    val db_server =
      if (server.defined) server
      else {
        open_server(options, host = host, port = port, ssh_host = ssh_host,
          ssh_port = ssh_port, ssh_user = ssh_user)
      }
    val server_close = !server.defined
    try {
      open_database(user = user, password = password, database = database,
        server = db_server, server_close = server_close)
    }
    catch { case exn: Throwable if server_close => db_server.close(); throw exn }
  }

  class Database private[PostgreSQL](
    val connection: Connection,
    print: String,
    server: SSH.Server,
    server_close: Boolean,
    receiver_delay: Time
  ) extends SQL.Database {
    override def toString: String = print

    override def now(): Date = {
      val now = SQL.Column.date("now")
      execute_query_statementO[Date]("SELECT NOW() as " + now.ident, res => res.date(now))
        .getOrElse(error("Failed to get current date/time from database server " + toString))
    }

    def sql_type(T: SQL.Type): SQL.Source = SQL.sql_type_postgresql(T)

    // see https://jdbc.postgresql.org/documentation/head/8-date-time.html
    def update_date(stmt: SQL.Statement, i: Int, date: Date): Unit =
      if (date == null) stmt.rep.setObject(i, null)
      else stmt.rep.setObject(i, OffsetDateTime.from(date.to(Date.timezone_utc).rep))

    def date(res: SQL.Result, column: SQL.Column): Date = {
      val obj = res.rep.getObject(column.name, classOf[OffsetDateTime])
      if (obj == null) null else Date.instant(obj.toInstant)
    }

    def insert_permissive(table: SQL.Table, sql: SQL.Source = ""): SQL.Source =
      table.insert_cmd(sql = if_proper(sql, sql + " ") + "ON CONFLICT DO NOTHING")

    override def destroy(table: SQL.Table): SQL.Source =
      super.destroy(table) + " CASCADE"


    /* explicit locking: only applicable to PostgreSQL within transaction context */
    // see https://www.postgresql.org/docs/14/sql-lock.html
    // see https://www.postgresql.org/docs/14/explicit-locking.html

    override def lock_tables(tables: List[SQL.Table]): PostgreSQL.Source =
      if_proper(tables, "LOCK TABLE " + tables.mkString(", ") + " IN ACCESS EXCLUSIVE MODE")


    /* notifications: IPC via database server */
    /*
      - see https://www.postgresql.org/docs/14/sql-notify.html
      - self-notifications and repeated notifications are suppressed
      - notifications are sorted by local system time (nano seconds)
      - receive() == None means that IPC is inactive or unavailable (SQLite)
    */

    private var _receiver_buffer: Option[Map[SQL.Notification, Long]] = None

    private lazy val _receiver_thread =
      Isabelle_Thread.fork(name = "PostgreSQL.receiver", daemon = true, uninterruptible = true) {
        val conn = the_postgresql_connection
        val self_pid = conn.getBackendPID

        try {
          while (true) {
            Isabelle_Thread.interruptible { receiver_delay.sleep(); Option(conn.getNotifications())}
            match {
              case Some(array) if array.nonEmpty =>
                synchronized {
                  var received = _receiver_buffer.getOrElse(Map.empty)
                  for (a <- array.iterator if a.getPID != self_pid) {
                    val msg = SQL.Notification(a.getName, a.getParameter)
                    if (!received.isDefinedAt(msg)) {
                      val stamp = System.nanoTime()
                      received = received + (msg -> stamp)
                    }
                  }
                  _receiver_buffer = Some(received)
                }
              case _ =>
            }
          }
        }
        catch { case Exn.Interrupt() => }
      }

    private def receiver_shutdown(): Unit = synchronized {
      if (_receiver_buffer.isDefined) {
        _receiver_thread.interrupt()
        Some(_receiver_thread)
      }
      else None
    }.foreach(_.join())

    private def synchronized_receiver[A](body: => A): A = synchronized {
      if (_receiver_buffer.isEmpty) {
        _receiver_buffer = Some(Map.empty)
        _receiver_thread
      }
      body
    }

    override def listen(channel: String): Unit = synchronized_receiver {
      execute_statement("LISTEN " + SQL.ident(channel))
    }

    override def unlisten(channel: String = "*"): Unit = synchronized_receiver {
      execute_statement("UNLISTEN " + (if (channel == "*") channel else SQL.ident(channel)))
    }

    override def send(channel: String, payload: String): Unit = synchronized_receiver {
      execute_statement(
        "NOTIFY " + SQL.ident(channel) + if_proper(payload, ", " + SQL.string(payload)))
    }

    override def receive(
      filter: SQL.Notification => Boolean = _ => true
    ): Option[List[SQL.Notification]] = synchronized {
      _receiver_buffer.map { received =>
        val filtered = received.keysIterator.filter(filter).toList
        if (filtered.nonEmpty) {
          _receiver_buffer = Some(received -- filtered)
          filtered.map(msg => msg -> received(msg)).sortBy(_._2).map(_._1)
        }
        else Nil
      }
    }

    override def close(): Unit = {
      receiver_shutdown()
      super.close()
      if (server_close) server.close()
    }
  }
}
