/*  Title:      Pure/General/sql.scala
    Author:     Makarius

Support for SQL databases: SQLite and PostgreSQL.
*/

package isabelle


import java.sql.{DriverManager, Connection, PreparedStatement, ResultSet}


object SQL
{
  /** SQL language **/

  /* concrete syntax */

  def quote_char(c: Char): String =
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
    quote(s.map(quote_char(_)).mkString)

  def quote_ident(s: String): String =
    quote(s.replace("\"", "\"\""))

  def enclosure(ss: Iterable[String]): String = ss.mkString("(", ", ", ")")


  /* types */

  object Type extends Enumeration
  {
    val Int = Value("INTEGER")
    val Long = Value("BIGINT")
    val Double = Value("DOUBLE PRECISION")
    val String = Value("TEXT")
    val Bytes = Value("BLOB")
  }

  type Type_Name = Type.Value => String
  def default_type_name(t: Type.Value): String = t.toString


  /* columns */

  object Column
  {
    def int(name: String, strict: Boolean = true, primary_key: Boolean = false): Column[Int] =
      new Column_Int(name, strict, primary_key)
    def long(name: String, strict: Boolean = true, primary_key: Boolean = false): Column[Long] =
      new Column_Long(name, strict, primary_key)
    def double(name: String, strict: Boolean = true, primary_key: Boolean = false): Column[Double] =
      new Column_Double(name, strict, primary_key)
    def string(name: String, strict: Boolean = true, primary_key: Boolean = false): Column[String] =
      new Column_String(name, strict, primary_key)
    def bytes(name: String, strict: Boolean = true, primary_key: Boolean = false): Column[Bytes] =
      new Column_Bytes(name, strict, primary_key)
  }

  abstract class Column[+A] private[SQL](
      val name: String,
      val strict: Boolean,
      val primary_key: Boolean,
      val sql_type: Type.Value) extends Function[ResultSet, A]
  {
    def sql_name: String = quote_ident(name)
    def sql_decl(type_name: Type_Name): String =
      sql_name + " " + type_name(sql_type) +
      (if (strict) " NOT NULL" else "") +
      (if (primary_key) " PRIMARY KEY" else "")

    def string(rs: ResultSet): String =
    {
      val s = rs.getString(name)
      if (s == null) "" else s
    }
    def apply(rs: ResultSet): A
    def get(rs: ResultSet): Option[A] =
    {
      val x = apply(rs)
      if (rs.wasNull) None else Some(x)
    }

    override def toString: String = sql_decl(default_type_name)
  }

  class Column_Int private[SQL](name: String, strict: Boolean, primary_key: Boolean)
    extends Column[Int](name, strict, primary_key, Type.Int)
  {
    def apply(rs: ResultSet): Int = rs.getInt(name)
  }

  class Column_Long private[SQL](name: String, strict: Boolean, primary_key: Boolean)
    extends Column[Long](name, strict, primary_key, Type.Long)
  {
    def apply(rs: ResultSet): Long = rs.getLong(name)
  }

  class Column_Double private[SQL](name: String, strict: Boolean, primary_key: Boolean)
    extends Column[Double](name, strict, primary_key, Type.Double)
  {
    def apply(rs: ResultSet): Double = rs.getDouble(name)
  }

  class Column_String private[SQL](name: String, strict: Boolean, primary_key: Boolean)
    extends Column[String](name, strict, primary_key, Type.String)
  {
    def apply(rs: ResultSet): String =
    {
      val s = rs.getString(name)
      if (s == null) "" else s
    }
  }

  class Column_Bytes private[SQL](name: String, strict: Boolean, primary_key: Boolean)
    extends Column[Bytes](name, strict, primary_key, Type.Bytes)
  {
    def apply(rs: ResultSet): Bytes =
    {
      val bs = rs.getBytes(name)
      if (bs == null) Bytes.empty else Bytes(bs)
    }
  }


  /* tables */

  def table(name: String, columns: List[Column[Any]]): Table = new Table(name, columns)

  class Table private[SQL](name: String, columns: List[Column[Any]])
  {
    private val columns_index: Map[String, Int] =
      columns.iterator.map(_.name).zipWithIndex.toMap

    Library.duplicates(columns.map(_.name)) match {
      case Nil =>
      case bad => error("Duplicate column names " + commas_quote(bad) + " for table " + quote(name))
    }

    columns.filter(_.primary_key) match {
      case bad if bad.length > 1 =>
        error("Multiple primary keys " + commas_quote(bad.map(_.name)) + " for table " + quote(name))
      case _ =>
    }

    def sql_create(strict: Boolean, rowid: Boolean, type_name: Type_Name): String =
      "CREATE TABLE " + (if (strict) "" else "IF NOT EXISTS ") +
        quote_ident(name) + " " + enclosure(columns.map(_.sql_decl(type_name))) +
        (if (rowid) "" else " WITHOUT ROWID")

    def sql_drop(strict: Boolean): String =
      "DROP TABLE " + (if (strict) "" else "IF EXISTS ") + quote_ident(name)

    def sql_create_index(
        index_name: String, index_columns: List[Column[Any]],
        strict: Boolean, unique: Boolean): String =
      "CREATE " + (if (unique) "UNIQUE " else "") + "INDEX " +
        (if (strict) "" else "IF NOT EXISTS ") + quote_ident(index_name) + " ON " +
        quote_ident(name) + " " + enclosure(index_columns.map(_.name))

    def sql_drop_index(index_name: String, strict: Boolean): String =
      "DROP INDEX " + (if (strict) "" else "IF EXISTS ") + quote_ident(index_name)

    def sql_insert: String =
      "INSERT INTO " + quote_ident(name) + " VALUES " + enclosure(columns.map(_ => "?"))

    def sql_select(select_columns: List[Column[Any]], distinct: Boolean): String =
      "SELECT " + (if (distinct) "DISTINCT " else "") +
      commas(select_columns.map(_.sql_name)) + " FROM " + quote_ident(name)

    override def toString: String =
      "TABLE " + quote_ident(name) + " " + enclosure(columns.map(_.toString))
  }


  /* results */

  def iterator[A](rs: ResultSet)(get: ResultSet => A): Iterator[A] = new Iterator[A]
  {
    private var _next: Boolean = rs.next()
    def hasNext: Boolean = _next
    def next: A = { val x = get(rs); _next = rs.next(); x }
  }



  /** SQL database operations **/

  trait Database
  {
    /* types */

    def type_name(t: Type.Value): String = default_type_name(t)


    /* connection */

    def connection: Connection

    def close() { connection.close }

    def transaction[A](body: => A): A =
    {
      val auto_commit = connection.getAutoCommit
      val savepoint = connection.setSavepoint

      try {
        connection.setAutoCommit(false)
        val result = body
        connection.commit
        result
      }
      catch { case exn: Throwable => connection.rollback(savepoint); throw exn }
      finally { connection.setAutoCommit(auto_commit) }
    }


    /* statements */

    def statement(sql: String): PreparedStatement = connection.prepareStatement(sql)

    def insert_statement(table: Table): PreparedStatement = statement(table.sql_insert)

    def select_statement(table: Table, columns: List[Column[Any]],
        sql: String = "", distinct: Boolean = false): PreparedStatement =
      statement(table.sql_select(columns, distinct) + (if (sql == "") "" else " " + sql))


    /* tables */

    def tables: List[String] =
      iterator(connection.getMetaData.getTables(null, null, "%", null))(_.getString(3)).toList

    def create_table(table: Table, strict: Boolean = true, rowid: Boolean = true): Unit =
      using(statement(table.sql_create(strict, rowid, type_name)))(_.execute())

    def drop_table(table: Table, strict: Boolean = true): Unit =
      using(statement(table.sql_drop(strict)))(_.execute())

    def create_index(table: Table, name: String, columns: List[Column[Any]],
        strict: Boolean = true, unique: Boolean = false): Unit =
      using(statement(table.sql_create_index(name, columns, strict, unique)))(_.execute())

    def drop_index(table: Table, name: String, strict: Boolean = true): Unit =
      using(statement(table.sql_drop_index(name, strict)))(_.execute())
  }
}



/** SQLite **/

object SQLite
{
  def open_database(path: Path): Database =
  {
    val path0 = path.expand
    val s0 = File.platform_path(path0)
    val s1 = if (Platform.is_windows) s0.replace('\\', '/') else s0
    val connection = DriverManager.getConnection("jdbc:sqlite:" + s1)
    new Database(path0.toString, connection)
  }

  class Database private[SQLite](name: String, val connection: Connection) extends SQL.Database
  {
    override def toString: String = name

    def rebuild { using(statement("VACUUM"))(_.execute()) }
  }
}



/** PostgreSQL **/

object PostgreSQL
{
  val default_port = 5432

  def open_database(
    user: String,
    password: String,
    database: String = "",
    host: String = "",
    port: Int = default_port,
    ssh: Option[SSH.Session] = None): Database =
  {
    require(user != "")

    val db_host = if (host != "") host else "localhost"
    val db_port = if (port != default_port) ":" + port else ""
    val db_name = "/" + (if (database != "") database else user)

    val (spec, port_forwarding) =
      ssh match {
        case None => (db_host + db_port + db_name, None)
        case Some(ssh) =>
          val fw = ssh.port_forwarding(remote_host = db_host, remote_port = port)
          ("localhost:" + fw.port + db_name, Some(fw))
      }
    try {
      val connection = DriverManager.getConnection("jdbc:postgresql://" + spec, user, password)
      new Database(user + "@" + spec, connection, port_forwarding)
    }
    catch { case exn: Throwable => port_forwarding.foreach(_.close); throw exn }
  }

  class Database private[PostgreSQL](
      name: String, val connection: Connection, port_forwarding: Option[SSH.Port_Forwarding])
    extends SQL.Database
  {
    override def toString: String =
      port_forwarding match {
        case None => name
        case Some(fw) => name + " via ssh " + fw.ssh
      }

    override def type_name(t: SQL.Type.Value): String =
      if (t == SQL.Type.Bytes) "BYTEA"
      else SQL.default_type_name(t)

    override def close() { super.close; port_forwarding.foreach(_.close) }
  }
}
