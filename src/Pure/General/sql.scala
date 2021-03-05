/*  Title:      Pure/General/sql.scala
    Author:     Makarius

Support for SQL databases: SQLite and PostgreSQL.
*/

package isabelle


import java.time.OffsetDateTime
import java.sql.{DriverManager, Connection, PreparedStatement, ResultSet}

import scala.collection.mutable


object SQL
{
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

  def select(columns: List[Column] = Nil, distinct: Boolean = false): Source =
    "SELECT " + (if (distinct) "DISTINCT " else "") +
    (if (columns.isEmpty) "*" else commas(columns.map(_.ident))) + " FROM "

  val join_outer: Source = " LEFT OUTER JOIN "
  val join_inner: Source = " INNER JOIN "
  def join(outer: Boolean): Source = if (outer) join_outer else join_inner

  def member(x: Source, set: Iterable[String]): Source =
    set.iterator.map(a => x + " = " + SQL.string(a)).mkString("(", " OR ", ")")


  /* types */

  object Type extends Enumeration
  {
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

  object Column
  {
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
    name: String, T: Type.Value, strict: Boolean = false, primary_key: Boolean = false,
    expr: SQL.Source = "")
  {
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

    def equal(s: String): Source = ident + " = " + string(s)
    def where_equal(s: String): Source = "WHERE " + equal(s)

    override def toString: Source = ident
  }


  /* tables */

  sealed case class Table(name: String, columns: List[Column], body: Source = "")
  {
    private val columns_index: Map[String, Int] =
      columns.iterator.map(_.name).zipWithIndex.toMap

    Library.duplicates(columns.map(_.name)) match {
      case Nil =>
      case bad => error("Duplicate column names " + commas_quote(bad) + " for table " + quote(name))
    }

    def ident: Source = SQL.ident(name)

    def query: Source =
      if (body == "") error("Missing SQL body for table " + quote(name))
      else SQL.enclose(body)

    def query_named: Source = query + " AS " + SQL.ident(name)

    def create(strict: Boolean = false, sql_type: Type.Value => Source): Source =
    {
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

    def insert_cmd(cmd: Source, sql: Source = ""): Source =
      cmd + " INTO " + ident + " VALUES " + enclosure(columns.map(_ => "?")) +
        (if (sql == "") "" else " " + sql)

    def insert(sql: Source = ""): Source = insert_cmd("INSERT", sql)

    def delete(sql: Source = ""): Source =
      "DELETE FROM " + ident +
        (if (sql == "") "" else " " + sql)

    def select(
        select_columns: List[Column] = Nil, sql: Source = "", distinct: Boolean = false): Source =
      SQL.select(select_columns, distinct = distinct) + ident +
        (if (sql == "") "" else " " + sql)

    override def toString: Source = ident
  }



  /** SQL database operations **/

  /* statements */

  class Statement private[SQL](val db: Database, val rep: PreparedStatement)
    extends AutoCloseable
  {
    stmt =>

    object bool
    {
      def update(i: Int, x: Boolean): Unit = rep.setBoolean(i, x)
      def update(i: Int, x: Option[Boolean]): Unit =
      {
        if (x.isDefined) update(i, x.get)
        else rep.setNull(i, java.sql.Types.BOOLEAN)
      }
    }
    object int
    {
      def update(i: Int, x: Int): Unit = rep.setInt(i, x)
      def update(i: Int, x: Option[Int]): Unit =
      {
        if (x.isDefined) update(i, x.get)
        else rep.setNull(i, java.sql.Types.INTEGER)
      }
    }
    object long
    {
      def update(i: Int, x: Long): Unit = rep.setLong(i, x)
      def update(i: Int, x: Option[Long]): Unit =
      {
        if (x.isDefined) update(i, x.get)
        else rep.setNull(i, java.sql.Types.BIGINT)
      }
    }
    object double
    {
      def update(i: Int, x: Double): Unit = rep.setDouble(i, x)
      def update(i: Int, x: Option[Double]): Unit =
      {
        if (x.isDefined) update(i, x.get)
        else rep.setNull(i, java.sql.Types.DOUBLE)
      }
    }
    object string
    {
      def update(i: Int, x: String): Unit = rep.setString(i, x)
      def update(i: Int, x: Option[String]): Unit = update(i, x.orNull)
    }
    object bytes
    {
      def update(i: Int, bytes: Bytes): Unit =
      {
        if (bytes == null) rep.setBytes(i, null)
        else rep.setBinaryStream(i, bytes.stream(), bytes.length)
      }
      def update(i: Int, bytes: Option[Bytes]): Unit = update(i, bytes.orNull)
    }
    object date
    {
      def update(i: Int, date: Date): Unit = db.update_date(stmt, i, date)
      def update(i: Int, date: Option[Date]): Unit = update(i, date.orNull)
    }

    def execute(): Boolean = rep.execute()
    def execute_query(): Result = new Result(this, rep.executeQuery())

    def close(): Unit = rep.close()
  }


  /* results */

  class Result private[SQL](val stmt: Statement, val rep: ResultSet)
  {
    res =>

    def next(): Boolean = rep.next()

    def iterator[A](get: Result => A): Iterator[A] = new Iterator[A]
    {
      private var _next: Boolean = res.next()
      def hasNext: Boolean = _next
      def next(): A = { val x = get(res); _next = res.next(); x }
    }

    def bool(column: Column): Boolean = rep.getBoolean(column.name)
    def int(column: Column): Int = rep.getInt(column.name)
    def long(column: Column): Long = rep.getLong(column.name)
    def double(column: Column): Double = rep.getDouble(column.name)
    def string(column: Column): String =
    {
      val s = rep.getString(column.name)
      if (s == null) "" else s
    }
    def bytes(column: Column): Bytes =
    {
      val bs = rep.getBytes(column.name)
      if (bs == null) Bytes.empty else Bytes(bs)
    }
    def date(column: Column): Date = stmt.db.date(res, column)

    def timing(c1: Column, c2: Column, c3: Column): Timing =
      Timing(Time.ms(long(c1)), Time.ms(long(c2)), Time.ms(long(c3)))

    def get[A](column: Column, f: Column => A): Option[A] =
    {
      val x = f(column)
      if (rep.wasNull) None else Some(x)
    }
    def get_bool(column: Column): Option[Boolean] = get(column, bool)
    def get_int(column: Column): Option[Int] = get(column, int)
    def get_long(column: Column): Option[Long] = get(column, long)
    def get_double(column: Column): Option[Double] = get(column, double)
    def get_string(column: Column): Option[String] = get(column, string)
    def get_bytes(column: Column): Option[Bytes] = get(column, bytes)
    def get_date(column: Column): Option[Date] = get(column, date)
  }


  /* database */

  trait Database extends AutoCloseable
  {
    db =>


    /* types */

    def sql_type(T: Type.Value): Source


    /* connection */

    def connection: Connection

    def close(): Unit = connection.close()

    def transaction[A](body: => A): A =
    {
      val auto_commit = connection.getAutoCommit
      try {
        connection.setAutoCommit(false)
        val savepoint = connection.setSavepoint
        try {
          val result = body
          connection.commit
          result
        }
        catch { case exn: Throwable => connection.rollback(savepoint); throw exn }
      }
      finally { connection.setAutoCommit(auto_commit) }
    }


    /* statements and results */

    def statement(sql: Source): Statement =
      new Statement(db, connection.prepareStatement(sql))

    def using_statement[A](sql: Source)(f: Statement => A): A =
      using(statement(sql))(f)

    def update_date(stmt: Statement, i: Int, date: Date): Unit
    def date(res: Result, column: Column): Date

    def insert_permissive(table: Table, sql: Source = ""): Source


    /* tables and views */

    def tables: List[String] =
    {
      val result = new mutable.ListBuffer[String]
      val rs = connection.getMetaData.getTables(null, null, "%", null)
      while (rs.next) { result += rs.getString(3) }
      result.toList
    }

    def create_table(table: Table, strict: Boolean = false, sql: Source = ""): Unit =
      using_statement(
        table.create(strict, sql_type) + (if (sql == "") "" else " " + sql))(_.execute())

    def create_index(table: Table, name: String, columns: List[Column],
        strict: Boolean = false, unique: Boolean = false): Unit =
      using_statement(table.create_index(name, columns, strict, unique))(_.execute())

    def create_view(table: Table, strict: Boolean = false): Unit =
    {
      if (strict || !tables.contains(table.name)) {
        val sql = "CREATE VIEW " + table + " AS " + { table.query; table.body }
        using_statement(sql)(_.execute())
      }
    }
  }
}



/** SQLite **/

object SQLite
{
  // see https://www.sqlite.org/lang_datefunc.html
  val date_format: Date.Format = Date.Format("uuuu-MM-dd HH:mm:ss.SSS x")

  lazy val init_jdbc: Unit =
  {
    val lib_path = Path.explode("$ISABELLE_SQLITE_HOME/" + Platform.jvm_platform)
    val lib_name =
      File.find_files(lib_path.file) match {
        case List(file) => file.getName
        case _ => error("Exactly one file expected in directory " + lib_path.expand)
      }
    System.setProperty("org.sqlite.lib.path", File.platform_path(lib_path))
    System.setProperty("org.sqlite.lib.name", lib_name)

    Class.forName("org.sqlite.JDBC")
  }

  def open_database(path: Path): Database =
  {
    init_jdbc
    val path0 = path.expand
    val s0 = File.platform_path(path0)
    val s1 = if (Platform.is_windows) s0.replace('\\', '/') else s0
    val connection = DriverManager.getConnection("jdbc:sqlite:" + s1)
    new Database(path0.toString, connection)
  }

  class Database private[SQLite](name: String, val connection: Connection) extends SQL.Database
  {
    override def toString: String = name

    def sql_type(T: SQL.Type.Value): SQL.Source = SQL.sql_type_sqlite(T)

    def update_date(stmt: SQL.Statement, i: Int, date: Date): Unit =
      if (date == null) stmt.string(i) = (null: String)
      else stmt.string(i) = date_format(date)

    def date(res: SQL.Result, column: SQL.Column): Date =
      date_format.parse(res.string(column))

    def insert_permissive(table: SQL.Table, sql: SQL.Source = ""): SQL.Source =
      table.insert_cmd("INSERT OR IGNORE", sql = sql)

    def rebuild: Unit = using_statement("VACUUM")(_.execute())
  }
}



/** PostgreSQL **/

object PostgreSQL
{
  val default_port = 5432

  lazy val init_jdbc: Unit = Class.forName("org.postgresql.Driver")

  def open_database(
    user: String,
    password: String,
    database: String = "",
    host: String = "",
    port: Int = 0,
    ssh: Option[SSH.Session] = None,
    ssh_close: Boolean = false): Database =
  {
    init_jdbc

    if (user == "") error("Undefined database user")

    val db_host = proper_string(host) getOrElse "localhost"
    val db_port = if (port > 0 && port != default_port) ":" + port else ""
    val db_name = "/" + (proper_string(database) getOrElse user)

    val (url, name, port_forwarding) =
      ssh match {
        case None =>
          val spec = db_host + db_port + db_name
          val url = "jdbc:postgresql://" + spec
          val name = user + "@" + spec
          (url, name, None)
        case Some(ssh) =>
          val fw =
            ssh.port_forwarding(remote_host = db_host,
              remote_port = if (port > 0) port else default_port,
              ssh_close = ssh_close)
          val url = "jdbc:postgresql://localhost:" + fw.local_port + db_name
          val name = user + "@" + fw + db_name + " via ssh " + ssh
          (url, name, Some(fw))
      }
    try {
      val connection = DriverManager.getConnection(url, user, password)
      new Database(name, connection, port_forwarding)
    }
    catch { case exn: Throwable => port_forwarding.foreach(_.close()); throw exn }
  }

  class Database private[PostgreSQL](
      name: String, val connection: Connection, port_forwarding: Option[SSH.Port_Forwarding])
    extends SQL.Database
  {
    override def toString: String = name

    def sql_type(T: SQL.Type.Value): SQL.Source = SQL.sql_type_postgresql(T)

    // see https://jdbc.postgresql.org/documentation/head/8-date-time.html
    def update_date(stmt: SQL.Statement, i: Int, date: Date): Unit =
      if (date == null) stmt.rep.setObject(i, null)
      else stmt.rep.setObject(i, OffsetDateTime.from(date.to(Date.timezone_utc).rep))

    def date(res: SQL.Result, column: SQL.Column): Date =
    {
      val obj = res.rep.getObject(column.name, classOf[OffsetDateTime])
      if (obj == null) null else Date.instant(obj.toInstant)
    }

    def insert_permissive(table: SQL.Table, sql: SQL.Source = ""): SQL.Source =
      table.insert_cmd("INSERT",
        sql = sql + (if (sql == "") "" else " ") + "ON CONFLICT DO NOTHING")

    override def close(): Unit = { super.close(); port_forwarding.foreach(_.close()) }
  }
}
