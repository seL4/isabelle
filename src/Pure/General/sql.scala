/*  Title:      Pure/General/sql.scala
    Author:     Makarius

Support for SQL databases: SQLite and PostgreSQL.
*/

package isabelle

import java.time.OffsetDateTime
import java.sql.{DriverManager, Connection, PreparedStatement, ResultSet}


object SQL
{
  /** SQL language **/

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

  def string(s: String): String =
    "'" + s.map(escape_char(_)).mkString + "'"

  def ident(s: String): String =
    Long_Name.implode(Long_Name.explode(s).map(a => quote(a.replace("\"", "\"\""))))

  def enclose(s: String): String = "(" + s + ")"
  def enclosure(ss: Iterable[String]): String = ss.mkString("(", ", ", ")")

  def select(columns: List[Column], distinct: Boolean = false): String =
    "SELECT " + (if (distinct) "DISTINCT " else "") + commas(columns.map(_.ident)) + " FROM "

  def join(table1: Table, table2: Table, sql: String = "", outer: Boolean = false): String =
    table1.ident + (if (outer) " LEFT OUTER JOIN " else " INNER JOIN ") + table2.ident +
      (if (sql == "") "" else " ON " + sql)

  def join_outer(table1: Table, table2: Table, sql: String = ""): String =
    join(table1, table2, sql, outer = true)


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

  def sql_type_default(T: Type.Value): String = T.toString

  def sql_type_sqlite(T: Type.Value): String =
    if (T == Type.Boolean) "INTEGER"
    else if (T == Type.Date) "TEXT"
    else sql_type_default(T)

  def sql_type_postgresql(T: Type.Value): String =
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
    name: String, T: Type.Value, strict: Boolean = false, primary_key: Boolean = false)
  {
    def apply(table: Table): Column =
      Column(Long_Name.qualify(table.name, name), T, strict = strict, primary_key = primary_key)

    def ident: String = SQL.ident(name)

    def decl(sql_type: Type.Value => String): String =
      ident + " " + sql_type(T) + (if (strict || primary_key) " NOT NULL" else "")

    def where_equal(s: String): String = "WHERE " + ident + " = " + string(s)

    override def toString: String = ident
  }


  /* tables */

  sealed case class Table(name: String, columns: List[Column], body: String = "")
  {
    private val columns_index: Map[String, Int] =
      columns.iterator.map(_.name).zipWithIndex.toMap

    Library.duplicates(columns.map(_.name)) match {
      case Nil =>
      case bad => error("Duplicate column names " + commas_quote(bad) + " for table " + quote(name))
    }

    def ident: String = SQL.ident(name)

    def query: String =
      if (body == "") error("Missing SQL body for table " + quote(name))
      else SQL.enclose(body)

    def query_alias(alias: String = name): String =
      query + " AS " + SQL.ident(alias)

    def create(strict: Boolean = false, sql_type: Type.Value => String): String =
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
        strict: Boolean = false, unique: Boolean = false): String =
      "CREATE " + (if (unique) "UNIQUE " else "") + "INDEX " +
        (if (strict) "" else "IF NOT EXISTS ") + SQL.ident(index_name) + " ON " +
        ident + " " + enclosure(index_columns.map(_.name))

    def insert_cmd(cmd: String, sql: String = ""): String =
      cmd + " INTO " + ident + " VALUES " + enclosure(columns.map(_ => "?")) +
        (if (sql == "") "" else " " + sql)

    def insert(sql: String = ""): String = insert_cmd("INSERT", sql)

    def delete(sql: String = ""): String =
      "DELETE FROM " + ident +
        (if (sql == "") "" else " " + sql)

    def select(select_columns: List[Column], sql: String = "", distinct: Boolean = false): String =
      SQL.select(select_columns, distinct = distinct) + ident +
        (if (sql == "") "" else " " + sql)

    override def toString: String = ident
  }



  /** SQL database operations **/

  /* results */

  def iterator[A](rs: ResultSet)(get: ResultSet => A): Iterator[A] = new Iterator[A]
  {
    private var _next: Boolean = rs.next()
    def hasNext: Boolean = _next
    def next: A = { val x = get(rs); _next = rs.next(); x }
  }

  trait Database
  {
    /* types */

    def sql_type(T: Type.Value): String


    /* connection */

    def connection: Connection

    def close() { connection.close }

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


    /* statements */

    def statement(sql: String): PreparedStatement =
      connection.prepareStatement(sql)

    def using_statement[A](sql: String)(f: PreparedStatement => A): A =
      using(statement(sql))(f)

    def insert_permissive(table: Table, sql: String = ""): String


    /* input */

    def set_bool(stmt: PreparedStatement, i: Int, x: Boolean) { stmt.setBoolean(i, x) }
    def set_bool(stmt: PreparedStatement, i: Int, x: Option[Boolean])
    {
      if (x.isDefined) set_bool(stmt, i, x.get)
      else stmt.setNull(i, java.sql.Types.BOOLEAN)
    }

    def set_int(stmt: PreparedStatement, i: Int, x: Int) { stmt.setInt(i, x) }
    def set_int(stmt: PreparedStatement, i: Int, x: Option[Int])
    {
      if (x.isDefined) set_int(stmt, i, x.get)
      else stmt.setNull(i, java.sql.Types.INTEGER)
    }

    def set_long(stmt: PreparedStatement, i: Int, x: Long) { stmt.setLong(i, x) }
    def set_long(stmt: PreparedStatement, i: Int, x: Option[Long])
    {
      if (x.isDefined) set_long(stmt, i, x.get)
      else stmt.setNull(i, java.sql.Types.BIGINT)
    }

    def set_double(stmt: PreparedStatement, i: Int, x: Double) { stmt.setDouble(i, x) }
    def set_double(stmt: PreparedStatement, i: Int, x: Option[Double])
    {
      if (x.isDefined) set_double(stmt, i, x.get)
      else stmt.setNull(i, java.sql.Types.DOUBLE)
    }

    def set_string(stmt: PreparedStatement, i: Int, x: String) { stmt.setString(i, x) }
    def set_string(stmt: PreparedStatement, i: Int, x: Option[String]): Unit =
      set_string(stmt, i, x.orNull)

    def set_bytes(stmt: PreparedStatement, i: Int, bytes: Bytes)
    {
      if (bytes == null) stmt.setBytes(i, null)
      else stmt.setBinaryStream(i, bytes.stream(), bytes.length)
    }
    def set_bytes(stmt: PreparedStatement, i: Int, bytes: Option[Bytes]): Unit =
      set_bytes(stmt, i, bytes.orNull)

    def set_date(stmt: PreparedStatement, i: Int, date: Date): Unit
    def set_date(stmt: PreparedStatement, i: Int, date: Option[Date]): Unit =
      set_date(stmt, i, date.orNull)


    /* output */

    def bool(rs: ResultSet, column: Column): Boolean = rs.getBoolean(column.name)
    def int(rs: ResultSet, column: Column): Int = rs.getInt(column.name)
    def long(rs: ResultSet, column: Column): Long = rs.getLong(column.name)
    def double(rs: ResultSet, column: Column): Double = rs.getDouble(column.name)
    def string(rs: ResultSet, column: Column): String =
    {
      val s = rs.getString(column.name)
      if (s == null) "" else s
    }
    def bytes(rs: ResultSet, column: Column): Bytes =
    {
      val bs = rs.getBytes(column.name)
      if (bs == null) Bytes.empty else Bytes(bs)
    }
    def date(rs: ResultSet, column: Column): Date

    def get[A](rs: ResultSet, column: Column, f: (ResultSet, Column) => A): Option[A] =
    {
      val x = f(rs, column)
      if (rs.wasNull) None else Some(x)
    }
    def get_bool(rs: ResultSet, column: Column): Option[Boolean] = get(rs, column, bool _)
    def get_int(rs: ResultSet, column: Column): Option[Int] = get(rs, column, int _)
    def get_long(rs: ResultSet, column: Column): Option[Long] = get(rs, column, long _)
    def get_double(rs: ResultSet, column: Column): Option[Double] = get(rs, column, double _)
    def get_string(rs: ResultSet, column: Column): Option[String] = get(rs, column, string _)
    def get_bytes(rs: ResultSet, column: Column): Option[Bytes] = get(rs, column, bytes _)
    def get_date(rs: ResultSet, column: Column): Option[Date] = get(rs, column, date _)


    /* tables and views */

    def tables: List[String] =
      iterator(connection.getMetaData.getTables(null, null, "%", null))(_.getString(3)).toList

    def create_table(table: Table, strict: Boolean = false, sql: String = ""): Unit =
      using_statement(
        table.create(strict, sql_type) + (if (sql == "") "" else " " + sql))(_.execute())

    def create_index(table: Table, name: String, columns: List[Column],
        strict: Boolean = false, unique: Boolean = false): Unit =
      using_statement(table.create_index(name, columns, strict, unique))(_.execute())

    def create_view(table: Table, strict: Boolean = false): Unit =
    {
      if (strict || !tables.contains(table.name)) {
        val sql = "CREATE VIEW " + table.ident + " AS " + { table.query; table.body }
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

  lazy val init_jdbc: Unit = Class.forName("org.sqlite.JDBC")

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

    def sql_type(T: SQL.Type.Value): String = SQL.sql_type_sqlite(T)

    def set_date(stmt: PreparedStatement, i: Int, date: Date): Unit =
      if (date == null) set_string(stmt, i, null: String)
      else set_string(stmt, i, date_format(date))

    def date(rs: ResultSet, column: SQL.Column): Date =
      date_format.parse(string(rs, column))

    def insert_permissive(table: SQL.Table, sql: String = ""): String =
      table.insert_cmd("INSERT OR IGNORE", sql = sql)

    def rebuild { using_statement("VACUUM")(_.execute()) }
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
    catch { case exn: Throwable => port_forwarding.foreach(_.close); throw exn }
  }

  class Database private[PostgreSQL](
      name: String, val connection: Connection, port_forwarding: Option[SSH.Port_Forwarding])
    extends SQL.Database
  {
    override def toString: String = name

    def sql_type(T: SQL.Type.Value): String = SQL.sql_type_postgresql(T)

    // see https://jdbc.postgresql.org/documentation/head/8-date-time.html
    def set_date(stmt: PreparedStatement, i: Int, date: Date): Unit =
      if (date == null) stmt.setObject(i, null)
      else stmt.setObject(i, OffsetDateTime.from(date.to_utc.rep))

    def date(rs: ResultSet, column: SQL.Column): Date =
    {
      val obj = rs.getObject(column.name, classOf[OffsetDateTime])
      if (obj == null) null else Date.instant(obj.toInstant)
    }

    def insert_permissive(table: SQL.Table, sql: String = ""): String =
      table.insert_cmd("INSERT",
        sql = sql + (if (sql == "") "" else " ") + "ON CONFLICT DO NOTHING")

    override def close() { super.close; port_forwarding.foreach(_.close) }
  }
}
