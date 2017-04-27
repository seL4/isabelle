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

  def quote_string(s: String): String =
    "'" + s.map(escape_char(_)).mkString + "'"

  def quote_ident(s: String): String =
    quote(s.replace("\"", "\"\""))

  def enclosure(ss: Iterable[String]): String = ss.mkString("(", ", ", ")")


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
    def sql_name: String = quote_ident(name)
    def sql_decl(sql_type: Type.Value => String): String =
      sql_name + " " + sql_type(T) + (if (strict || primary_key) " NOT NULL" else "")

    def sql_where_eq: String = "WHERE " + sql_name + " = "
    def sql_where_eq_string(s: String): String = sql_where_eq + quote_string(s)

    override def toString: String = sql_decl(sql_type_default)
  }


  /* tables */

  sealed case class Table(name: String, columns: List[Column])
  {
    private val columns_index: Map[String, Int] =
      columns.iterator.map(_.name).zipWithIndex.toMap

    Library.duplicates(columns.map(_.name)) match {
      case Nil =>
      case bad => error("Duplicate column names " + commas_quote(bad) + " for table " + quote(name))
    }

    def sql_columns(sql_type: Type.Value => String): String =
    {
      val primary_key =
        columns.filter(_.primary_key).map(_.name) match {
          case Nil => Nil
          case keys => List("PRIMARY KEY " + enclosure(keys))
        }
      enclosure(columns.map(_.sql_decl(sql_type)) ::: primary_key)
    }

    def sql_create(strict: Boolean, sql_type: Type.Value => String): String =
      "CREATE TABLE " + (if (strict) "" else "IF NOT EXISTS ") +
        quote_ident(name) + " " + sql_columns(sql_type)

    def sql_drop(strict: Boolean): String =
      "DROP TABLE " + (if (strict) "" else "IF EXISTS ") + quote_ident(name)

    def sql_create_index(
        index_name: String, index_columns: List[Column],
        strict: Boolean, unique: Boolean): String =
      "CREATE " + (if (unique) "UNIQUE " else "") + "INDEX " +
        (if (strict) "" else "IF NOT EXISTS ") + quote_ident(index_name) + " ON " +
        quote_ident(name) + " " + enclosure(index_columns.map(_.name))

    def sql_drop_index(index_name: String, strict: Boolean): String =
      "DROP INDEX " + (if (strict) "" else "IF EXISTS ") + quote_ident(index_name)

    def sql_insert: String =
      "INSERT INTO " + quote_ident(name) + " VALUES " + enclosure(columns.map(_ => "?"))

    def sql_delete: String =
      "DELETE FROM " + quote_ident(name)

    def sql_select(select_columns: List[Column], distinct: Boolean): String =
      "SELECT " + (if (distinct) "DISTINCT " else "") +
      commas(select_columns.map(_.sql_name)) + " FROM " + quote_ident(name)

    override def toString: String =
      "TABLE " + quote_ident(name) + " " + sql_columns(sql_type_default)
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

    def statement(sql: String): PreparedStatement = connection.prepareStatement(sql)

    def insert_statement(table: Table): PreparedStatement = statement(table.sql_insert)

    def delete_statement(table: Table, sql: String = ""): PreparedStatement =
      statement(table.sql_delete + (if (sql == "") "" else " " + sql))

    def select_statement(table: Table, columns: List[Column],
        sql: String = "", distinct: Boolean = false): PreparedStatement =
      statement(table.sql_select(columns, distinct) + (if (sql == "") "" else " " + sql))


    /* input */

    def set_bool(stmt: PreparedStatement, i: Int, x: Boolean) { stmt.setBoolean(i, x) }
    def set_int(stmt: PreparedStatement, i: Int, x: Int) { stmt.setInt(i, x) }
    def set_long(stmt: PreparedStatement, i: Int, x: Long) { stmt.setLong(i, x) }
    def set_double(stmt: PreparedStatement, i: Int, x: Double) { stmt.setDouble(i, x) }
    def set_string(stmt: PreparedStatement, i: Int, x: String) { stmt.setString(i, x) }
    def set_bytes(stmt: PreparedStatement, i: Int, bytes: Bytes)
    { stmt.setBinaryStream(i, bytes.stream(), bytes.length) }
    def set_date(stmt: PreparedStatement, i: Int, date: Date)


    /* output */

    def bool(rs: ResultSet, name: String): Boolean = rs.getBoolean(name)
    def int(rs: ResultSet, name: String): Int = rs.getInt(name)
    def long(rs: ResultSet, name: String): Long = rs.getLong(name)
    def double(rs: ResultSet, name: String): Double = rs.getDouble(name)
    def string(rs: ResultSet, name: String): String =
    {
      val s = rs.getString(name)
      if (s == null) "" else s
    }
    def bytes(rs: ResultSet, name: String): Bytes =
    {
      val bs = rs.getBytes(name)
      if (bs == null) Bytes.empty else Bytes(bs)
    }
    def date(rs: ResultSet, name: String): Date

    def bool(rs: ResultSet, column: Column): Boolean = bool(rs, column.name)
    def int(rs: ResultSet, column: Column): Int = int(rs, column.name)
    def long(rs: ResultSet, column: Column): Long = long(rs, column.name)
    def double(rs: ResultSet, column: Column): Double = double(rs, column.name)
    def string(rs: ResultSet, column: Column): String = string(rs, column.name)
    def bytes(rs: ResultSet, column: Column): Bytes = bytes(rs, column.name)
    def date(rs: ResultSet, column: Column): Date = date(rs, column.name)

    def get[A, B](rs: ResultSet, a: A, f: (ResultSet, A) => B): Option[B] =
    {
      val x = f(rs, a)
      if (rs.wasNull) None else Some(x)
    }


    /* tables */

    def tables: List[String] =
      iterator(connection.getMetaData.getTables(null, null, "%", null))(_.getString(3)).toList

    def create_table(table: Table, strict: Boolean = false, sql: String = ""): Unit =
      using(statement(table.sql_create(strict, sql_type) + (if (sql == "") "" else " " + sql)))(
        _.execute())

    def drop_table(table: Table, strict: Boolean = false): Unit =
      using(statement(table.sql_drop(strict)))(_.execute())

    def create_index(table: Table, name: String, columns: List[Column],
        strict: Boolean = false, unique: Boolean = false): Unit =
      using(statement(table.sql_create_index(name, columns, strict, unique)))(_.execute())

    def drop_index(table: Table, name: String, strict: Boolean = false): Unit =
      using(statement(table.sql_drop_index(name, strict)))(_.execute())
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
      set_string(stmt, i, date_format(date))
    def date(rs: ResultSet, name: String): Date =
      date_format.parse(string(rs, name))

    def rebuild { using(statement("VACUUM"))(_.execute()) }
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
    port: Int = default_port,
    ssh: Option[SSH.Session] = None): Database =
  {
    init_jdbc

    require(user != "")

    val db_host = if (host != "") host else "localhost"
    val db_port = if (port != default_port) ":" + port else ""
    val db_name = "/" + (if (database != "") database else user)

    val (url, name, port_forwarding) =
      ssh match {
        case None =>
          val spec = db_host + db_port + db_name
          val url = "jdbc:postgresql://" + spec
          val name = user + "@" + spec
          (url, name, None)
        case Some(ssh) =>
          val fw = ssh.port_forwarding(remote_host = db_host, remote_port = port)
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
      stmt.setObject(i, OffsetDateTime.from(date.to_utc.rep))
    def date(rs: ResultSet, name: String): Date =
      Date.instant(rs.getObject(name, classOf[OffsetDateTime]).toInstant)

    override def close() { super.close; port_forwarding.foreach(_.close) }
  }
}
