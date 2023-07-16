/*  Title:      Pure/General/sql.scala
    Author:     Makarius

Support for SQL databases: SQLite and PostgreSQL.

See https://docs.oracle.com/en/java/javase/17/docs/api/java.sql/java/sql/Connection.html
*/

package isabelle


import java.time.OffsetDateTime
import java.sql.{DriverManager, Connection, PreparedStatement, ResultSet}

import org.sqlite.jdbc4.JDBC4Connection
import org.postgresql.{PGConnection, PGNotification}

import scala.collection.mutable


object SQL {
  /** SQL language **/

  type Source = String


  /* concrete syntax */

  def escape_char(c: Char): String =
    c match {
      case '\u0000' => "\\0"
      case '\'' => "\\'"
      case '\"' => "\\\""
      case '\b' => "\\b"
      case '\n' => "\\n"
      case '\r' => "\\r"
      case '\t' => "\\t"
      case '\u001a' => "\\Z"
      case '\\' => "\\\\"
      case _ => c.toString
    }

  def string(s: String): Source =
    s.iterator.map(escape_char).mkString("'", "", "'")

  def ident(s: String): Source =
    Long_Name.implode(Long_Name.explode(s).map(a => quote(a.replace("\"", "\"\""))))

  def enclose(s: Source): Source = "(" + s + ")"
  def enclosure(ss: Iterable[Source]): Source = ss.mkString("(", ", ", ")")

  def separate(sql: Source): Source =
    (if (sql.isEmpty || sql.startsWith(" ")) "" else " ") + sql

  def select(columns: List[Column] = Nil, distinct: Boolean = false, sql: Source = ""): Source =
    "SELECT " + (if (distinct) "DISTINCT " else "") +
    (if (columns.isEmpty) "*" else commas(columns.map(_.ident))) + " FROM " + sql

  val join_outer: Source = " LEFT OUTER JOIN "
  val join_inner: Source = " INNER JOIN "
  def join(outer: Boolean): Source = if (outer) join_outer else join_inner

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

  def member(sql: Source, set: Iterable[String]): Source =
    if (set.isEmpty) FALSE
    else OR(set.iterator.map(equal(sql, _)).toList)

  def where(sql: Source): Source = if_proper(sql, " WHERE " + sql)
  def where_and(args: Source*): Source = where(and(args:_*))
  def where_or(args: Source*): Source = where(or(args:_*))


  /* types */

  object Type extends Enumeration {
    val Boolean = Value("BOOLEAN")
    val Int = Value("INTEGER")
    val Long = Value("BIGINT")
    val Double = Value("DOUBLE PRECISION")
    val String = Value("TEXT")
    val Bytes = Value("BLOB")
    val Date = Value("TIMESTAMP WITH TIME ZONE")
  }

  def sql_type_default(T: Type.Value): Source = T.toString

  def sql_type_sqlite(T: Type.Value): Source =
    if (T == Type.Boolean) "INTEGER"
    else if (T == Type.Date) "TEXT"
    else sql_type_default(T)

  def sql_type_postgresql(T: Type.Value): Source =
    if (T == Type.Bytes) "BYTEA"
    else sql_type_default(T)


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
    T: Type.Value,
    strict: Boolean = false,
    primary_key: Boolean = false,
    expr: SQL.Source = ""
  ) {
    def make_primary_key: Column = copy(primary_key = true)

    def apply(table: Table): Column =
      Column(Long_Name.qualify(table.name, name), T, strict = strict, primary_key = primary_key)

    def ident: Source =
      if (expr == "") SQL.ident(name)
      else enclose(expr) + " AS " + SQL.ident(name)

    def decl(sql_type: Type.Value => Source): Source =
      ident + " " + sql_type(T) + (if (strict || primary_key) " NOT NULL" else "")

    def defined: String = ident + " IS NOT NULL"
    def undefined: String = ident + " IS NULL"

    def equal(x: Int): Source = SQL.equal(ident, x)
    def equal(x: Long): Source = SQL.equal(ident, x)
    def equal(x: String): Source = SQL.equal(ident, x)

    def where_equal(x: Int): Source = SQL.where(equal(x))
    def where_equal(x: Long): Source = SQL.where(equal(x))
    def where_equal(x: String): Source = SQL.where(equal(x))

    def member(set: Iterable[String]): Source = SQL.member(ident, set)
    def where_member(set: Iterable[String]): Source = SQL.where(member(set))

    def max: Column = copy(expr = "MAX(" + ident + ")")

    override def toString: Source = ident
  }

  def order_by(columns: List[Column], descending: Boolean = false): Source =
    " ORDER BY " + columns.mkString(", ") + (if (descending) " DESC" else "")


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

    def create(strict: Boolean, sql_type: Type.Value => Source): Source = {
      val primary_key =
        columns.filter(_.primary_key).map(_.name) match {
          case Nil => Nil
          case keys => List("PRIMARY KEY " + enclosure(keys))
        }
      "CREATE TABLE " + (if (strict) "" else "IF NOT EXISTS ") +
        ident + " " + enclosure(columns.map(_.decl(sql_type)) ::: primary_key)
    }

    def create_index(index_name: String, index_columns: List[Column],
        strict: Boolean = false, unique: Boolean = false): Source =
      "CREATE " + (if (unique) "UNIQUE " else "") + "INDEX " +
        (if (strict) "" else "IF NOT EXISTS ") + SQL.ident(index_name) + " ON " +
        ident + " " + enclosure(index_columns.map(_.name))

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
    val empty: Tables = list(Nil)
    def apply(args: Table*): Tables = list(args.toList)
  }

  final class Tables private(val list: List[Table]) extends Iterable[Table] {
    override def toString: String = list.mkString("SQL.Tables(", ", ", ")")

    def ::: (other: Tables): Tables = new Tables(other.list ::: list)

    def iterator: Iterator[Table] = list.iterator

    // requires transaction
    def lock(db: Database, create: Boolean = false): Boolean = {
      if (create) foreach(db.create_table(_))
      val sql = db.lock_tables(list)
      if (sql.nonEmpty) { db.execute_statement(sql); true }
      else false
    }
  }

  abstract class Data(table_prefix: String = "") {
    def tables: Tables = Tables.empty

    def transaction_lock[A](
      db: Database,
      create: Boolean = false,
      label: String = "",
      log: Logger = new System_Logger,
      synchronized: Boolean = false,
    )(body: => A): A = {
      def run: A = db.transaction_lock(tables, create = create, label = label, log = log)(body)
      if (synchronized) db.synchronized { run } else run
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
        else rep.setBinaryStream(i, bytes.stream(), bytes.length)
      }
      def update(i: Int, bytes: Option[Bytes]): Unit = update(i, bytes.orNull)
    }
    object date {
      def update(i: Int, date: Date): Unit = db.update_date(stmt, i, date)
      def update(i: Int, date: Option[Date]): Unit = update(i, date.orNull)
    }

    def execute(): Boolean = rep.execute()
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


  /* database */

  trait Database extends AutoCloseable {
    db =>

    def is_sqlite: Boolean = isInstanceOf[SQLite.Database]
    def is_postgresql: Boolean = isInstanceOf[PostgreSQL.Database]

    def vacuum(tables: SQL.Tables = SQL.Tables.empty): Unit =
      if (tables.list.nonEmpty) {
        postgresql_major_version match {
          case Some(m) if m <= 10 =>
            for (table <- tables) execute_statement("VACUUM " + table.ident)
          case Some(_) =>
            execute_statement("VACUUM" + commas(tables.list.map(_.ident)))
          case None => execute_statement("VACUUM")
        }
      }

    def now(): Date


    /* types */

    def sql_type(T: Type.Value): Source


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

    def transaction[A](body: => A): A = {
      val auto_commit = connection.getAutoCommit()
      try {
        connection.setAutoCommit(false)
        val savepoint = connection.setSavepoint()
        try {
          val result = body
          connection.commit()
          result
        }
        catch { case exn: Throwable => connection.rollback(savepoint); throw exn }
      }
      finally { connection.setAutoCommit(auto_commit) }
    }

    def transaction_lock[A](
      tables: Tables,
      create: Boolean = false,
      label: String = "",
      log: Logger = new System_Logger
    )(body: => A): A = {
      val prop = "isabelle.transaction_trace"
      val trace_min =
        System.getProperty(prop, "") match {
          case Value.Long(ms) => Time.ms(ms)
          case "true" => Time.min
          case "false" | "" => Time.max
          case s => error("Bad system property " + prop + ": " + quote(s))
        }

      val trace_count = - SQL.transaction_count()
      val trace_start = Time.now()
      var trace_nl = false

      def trace(msg: String, nl: Boolean = false): Unit = {
        val trace_time = Time.now() - trace_start
        if (trace_time >= trace_min) {
          val nl = if (trace_nl) "" else { trace_nl = true; "\n" }
          log(nl + trace_time + " transaction " + trace_count +
            if_proper(label, " " + label) + ": " + msg)
        }
      }

      val res =
        transaction {
          trace("begin")
          if (tables.lock(db, create = create)) trace("locked")
          val res = Exn.capture { body }
          trace("end")
          res
        }
      trace("commit")
      Exn.release(res)
    }

    def lock_tables(tables: List[Table]): Source = ""  // PostgreSQL only


    /* statements and results */

    def statement(sql: Source): Statement =
      new Statement(db, connection.prepareStatement(sql))

    def using_statement[A](sql: Source)(f: Statement => A): A =
      using(statement(sql))(f)

    def execute_statement(sql: Source, body: Statement => Unit = _ => ()): Unit =
      using_statement(sql) { stmt => body(stmt); stmt.execute() }

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


    /* tables and views */

    def tables: List[String] = {
      val result = new mutable.ListBuffer[String]
      val rs = connection.getMetaData.getTables(null, null, "%", null)
      while (rs.next) { result += rs.getString(3) }
      result.toList
    }

    def create_table(table: Table, strict: Boolean = false, sql: Source = ""): Unit = {
      execute_statement(table.create(strict, sql_type) + SQL.separate(sql))
      if (is_postgresql) {
        for (column <- table.columns if column.T == SQL.Type.Bytes) {
          execute_statement(
            "ALTER TABLE " + table + " ALTER COLUMN " + column + " SET STORAGE EXTERNAL")
        }
      }
    }

    def create_index(table: Table, name: String, columns: List[Column],
        strict: Boolean = false, unique: Boolean = false): Unit =
      execute_statement(table.create_index(name, columns, strict, unique))

    def create_view(table: Table, strict: Boolean = false): Unit = {
      if (strict || !tables.contains(table.name)) {
        execute_statement("CREATE VIEW " + table + " AS " + { table.query; table.body })
      }
    }
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
    val connection = DriverManager.getConnection("jdbc:sqlite:" + s1)
    val db = new Database(path0.toString, connection)

    try { if (restrict) File.restrict(path0) }
    catch { case exn: Throwable => db.close(); throw exn }

    db
  }

  class Database private[SQLite](name: String, val connection: Connection) extends SQL.Database {
    override def toString: String = name

    override def now(): Date = Date.now()

    def sql_type(T: SQL.Type.Value): SQL.Source = SQL.sql_type_sqlite(T)

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

// see https://www.postgresql.org/docs/current/index.html
// see https://jdbc.postgresql.org/documentation

object PostgreSQL {
  type Source = SQL.Source

  lazy val init_jdbc: Unit = Class.forName("org.postgresql.Driver")

  val default_server: SSH.Server = SSH.local_server(port = 5432)

  def open_database_server(
    options: Options,
    user: String = "",
    password: String = "",
    database: String = "",
    host: String = "",
    port: Int = 0,
    ssh_host: String = "",
    ssh_port: Int = 0,
    ssh_user: String = "",
    server: SSH.Server = SSH.no_server
  ): PostgreSQL.Database = {
    val (db_server, server_close) =
      if (server.defined) (server, false)
      else {
        val server_host = proper_string(host).getOrElse(default_server.host)
        val server_port = if (port > 0) port else default_server.port
        val db_server =
          if (ssh_host.isEmpty) SSH.local_server(host = server_host, port = server_port)
          else {
            SSH.open_server(options, host = ssh_host, port = ssh_port, user = ssh_user,
              remote_host = server_host, remote_port = server_port)
          }
        (db_server, true)
      }

    try {
      open_database(user = user, password = password, database = database,
        server = db_server, server_close = server_close)
    }
    catch { case exn: Throwable => if (server_close) db_server.close(); throw exn }
  }

  def open_database(
    user: String,
    password: String,
    database: String = "",
    server: SSH.Server = default_server,
    server_close: Boolean = false,
  ): Database = {
    init_jdbc

    if (user.isEmpty) error("Undefined database user")
    if (server.host.isEmpty) error("Undefined database server host")
    if (server.port <= 0) error("Undefined database server port")

    val name = proper_string(database) getOrElse user
    val url = "jdbc:postgresql://" + server.host + ":" + server.port + "/" + name
    val ssh = server.ssh_system.ssh_session
    val print = user + "@" + server + "/" + name + if_proper(ssh, " via ssh " + ssh.get)

    val connection = DriverManager.getConnection(url, user, password)
    new Database(connection, print, server, server_close)
  }

  class Database private[PostgreSQL](
    val connection: Connection,
    print: String,
    server: SSH.Server,
    server_close: Boolean
  ) extends SQL.Database {
    override def toString: String = print

    override def now(): Date = {
      val now = SQL.Column.date("now")
      execute_query_statementO[Date]("SELECT NOW() as " + now.ident, res => res.date(now))
        .getOrElse(error("Failed to get current date/time from database server " + toString))
    }

    def sql_type(T: SQL.Type.Value): SQL.Source = SQL.sql_type_postgresql(T)

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


    /* explicit locking: only applicable to PostgreSQL within transaction context */
    // see https://www.postgresql.org/docs/current/sql-lock.html
    // see https://www.postgresql.org/docs/current/explicit-locking.html

    override def lock_tables(tables: List[SQL.Table]): PostgreSQL.Source =
      if_proper(tables, "LOCK TABLE " + tables.mkString(", ") + " IN ACCESS EXCLUSIVE MODE")


    /* notifications: IPC via database server */
    // see https://www.postgresql.org/docs/current/sql-notify.html

    def listen(name: String): Unit =
      execute_statement("LISTEN " + SQL.ident(name))

    def unlisten(name: String = "*"): Unit =
      execute_statement("UNLISTEN " + (if (name == "*") name else SQL.ident(name)))

    def notify(name: String, payload: String = ""): Unit =
      execute_statement("NOTIFY " + SQL.ident(name) + if_proper(payload, ", " + SQL.string(payload)))

    def get_notifications(): List[PGNotification] =
      the_postgresql_connection.getNotifications() match {
        case null => Nil
        case array => array.toList
      }


    override def close(): Unit = { super.close(); if (server_close) server.close() }
  }
}
