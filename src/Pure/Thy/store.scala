/*  Title:      Pure/Thy/store.scala
    Author:     Makarius

Persistent store for session content: within file-system and/or SQL database.
*/

package isabelle


import java.sql.SQLException


object Store {
  def apply(options: Options, cache: Term.Cache = Term.Cache.make()): Store =
    new Store(options, cache)


  /* session build info */

  sealed case class Build_Info(
    sources: SHA1.Shasum,
    input_heaps: SHA1.Shasum,
    output_heap: SHA1.Shasum,
    return_code: Int,
    uuid: String
  ) {
    def ok: Boolean = return_code == 0
  }


  /* session sources */

  sealed case class Source_File(
    name: String,
    digest: SHA1.Digest,
    compressed: Boolean,
    body: Bytes,
    cache: Compress.Cache
  ) {
    override def toString: String = name

    def bytes: Bytes = if (compressed) body.uncompress(cache = cache) else body
  }

  object Sources {
    def load(session_base: Sessions.Base, cache: Compress.Cache = Compress.Cache.none): Sources =
      new Sources(
        session_base.session_sources.foldLeft(Map.empty) {
          case (sources, (path, digest)) =>
            def err(): Nothing = error("Incoherent digest for source file: " + path)
            val name = File.symbolic_path(path)
            sources.get(name) match {
              case Some(source_file) =>
                if (source_file.digest == digest) sources else err()
              case None =>
                val bytes = Bytes.read(path)
                if (bytes.sha1_digest == digest) {
                  val (compressed, body) =
                    bytes.maybe_compress(Compress.Options_Zstd(), cache = cache)
                  val file = Source_File(name, digest, compressed, body, cache)
                  sources + (name -> file)
                }
                else err()
            }
        })
  }

  class Sources private(rep: Map[String, Source_File]) extends Iterable[Source_File] {
    override def toString: String = rep.values.toList.sortBy(_.name).mkString("Sources(", ", ", ")")
    override def iterator: Iterator[Source_File] = rep.valuesIterator

    def get(name: String): Option[Source_File] = rep.get(name)
    def apply(name: String): Source_File =
      get(name).getOrElse(error("Missing session sources entry " + quote(name)))
  }


  /* SQL data model */

  object Data extends SQL.Data() {
    override lazy val tables = SQL.Tables(Session_Info.table, Sources.table)

    object Session_Info {
      val session_name = SQL.Column.string("session_name").make_primary_key

      // Build_Log.Session_Info
      val session_timing = SQL.Column.bytes("session_timing")
      val command_timings = SQL.Column.bytes("command_timings")
      val theory_timings = SQL.Column.bytes("theory_timings")
      val ml_statistics = SQL.Column.bytes("ml_statistics")
      val task_statistics = SQL.Column.bytes("task_statistics")
      val errors = SQL.Column.bytes("errors")
      val build_log_columns =
        List(session_name, session_timing, command_timings, theory_timings,
          ml_statistics, task_statistics, errors)

      // Build_Info
      val sources = SQL.Column.string("sources")
      val input_heaps = SQL.Column.string("input_heaps")
      val output_heap = SQL.Column.string("output_heap")
      val return_code = SQL.Column.int("return_code")
      val uuid = SQL.Column.string("uuid")
      val build_columns = List(sources, input_heaps, output_heap, return_code, uuid)

      val table = SQL.Table("isabelle_session_info", build_log_columns ::: build_columns)

      val augment_table: PostgreSQL.Source =
        "ALTER TABLE IF EXISTS " + table.ident +
        " ADD COLUMN IF NOT EXISTS " + uuid.decl(SQL.sql_type_postgresql)
    }

    object Sources {
      val session_name = SQL.Column.string("session_name").make_primary_key
      val name = SQL.Column.string("name").make_primary_key
      val digest = SQL.Column.string("digest")
      val compressed = SQL.Column.bool("compressed")
      val body = SQL.Column.bytes("body")

      val table =
        SQL.Table("isabelle_sources", List(session_name, name, digest, compressed, body))

      def where_equal(session_name: String, name: String = ""): SQL.Source =
        SQL.where_and(
          Sources.session_name.equal(session_name),
          if_proper(name, Sources.name.equal(name)))
    }

    def read_bytes(db: SQL.Database, name: String, column: SQL.Column): Bytes =
      db.execute_query_statementO[Bytes](
        Session_Info.table.select(List(column), sql = Session_Info.session_name.where_equal(name)),
        res => res.bytes(column)
      ).getOrElse(Bytes.empty)

    def read_properties(
      db: SQL.Database, name: String, column: SQL.Column, cache: Term.Cache
    ): List[Properties.T] = Properties.uncompress(read_bytes(db, name, column), cache = cache)

    def read_session_timing(db: SQL.Database, name: String, cache: Term.Cache): Properties.T =
      Properties.decode(read_bytes(db, name, Session_Info.session_timing), cache = cache)

    def read_command_timings(db: SQL.Database, name: String): Bytes =
      read_bytes(db, name, Session_Info.command_timings)

    def read_theory_timings(db: SQL.Database, name: String, cache: Term.Cache): List[Properties.T] =
      read_properties(db, name, Session_Info.theory_timings, cache)

    def read_ml_statistics(db: SQL.Database, name: String, cache: Term.Cache): List[Properties.T] =
      read_properties(db, name, Session_Info.ml_statistics, cache)

    def read_task_statistics(db: SQL.Database, name: String, cache: Term.Cache): List[Properties.T] =
      read_properties(db, name, Session_Info.task_statistics, cache)

    def read_errors(db: SQL.Database, name: String, cache: Term.Cache): List[String] =
      Build_Log.uncompress_errors(read_bytes(db, name, Session_Info.errors), cache = cache)

    def read_build(db: SQL.Database, name: String): Option[Store.Build_Info] = {
      if (db.tables.contains(Session_Info.table.name)) {
        db.execute_query_statementO[Store.Build_Info](
          Session_Info.table.select(sql = Session_Info.session_name.where_equal(name)),
          { res =>
            val uuid =
              try { Option(res.string(Session_Info.uuid)).getOrElse("") }
              catch { case _: SQLException => "" }
            Store.Build_Info(
              SHA1.fake_shasum(res.string(Session_Info.sources)),
              SHA1.fake_shasum(res.string(Session_Info.input_heaps)),
              SHA1.fake_shasum(res.string(Session_Info.output_heap)),
              res.int(Session_Info.return_code),
              uuid)
          }
        )
      }
      else None
    }

    def write_session_info(
      db: SQL.Database,
      cache: Compress.Cache,
      session_name: String,
      build_log: Build_Log.Session_Info,
      build: Build_Info
    ): Unit = {
      db.execute_statement(Session_Info.table.insert(), body =
        { stmt =>
          stmt.string(1) = session_name
          stmt.bytes(2) = Properties.encode(build_log.session_timing)
          stmt.bytes(3) = Properties.compress(build_log.command_timings, cache = cache)
          stmt.bytes(4) = Properties.compress(build_log.theory_timings, cache = cache)
          stmt.bytes(5) = Properties.compress(build_log.ml_statistics, cache = cache)
          stmt.bytes(6) = Properties.compress(build_log.task_statistics, cache = cache)
          stmt.bytes(7) = Build_Log.compress_errors(build_log.errors, cache = cache)
          stmt.string(8) = build.sources.toString
          stmt.string(9) = build.input_heaps.toString
          stmt.string(10) = build.output_heap.toString
          stmt.int(11) = build.return_code
          stmt.string(12) = build.uuid
        })
    }

    def write_sources(db: SQL.Database, session_name: String, sources: Sources): Unit =
      for (source_file <- sources) {
        db.execute_statement(Sources.table.insert(), body =
          { stmt =>
            stmt.string(1) = session_name
            stmt.string(2) = source_file.name
            stmt.string(3) = source_file.digest.toString
            stmt.bool(4) = source_file.compressed
            stmt.bytes(5) = source_file.body
          })
      }

    def read_sources(
      db: SQL.Database,
      session_name: String,
      name: String,
      cache: Compress.Cache
    ): List[Source_File] = {
      db.execute_query_statement(
        Sources.table.select(
          sql = Sources.where_equal(session_name, name = name) + SQL.order_by(List(Sources.name))),
        List.from[Source_File],
        { res =>
          val res_name = res.string(Sources.name)
          val digest = SHA1.fake_digest(res.string(Sources.digest))
          val compressed = res.bool(Sources.compressed)
          val body = res.bytes(Sources.body)
          Source_File(res_name, digest, compressed, body, cache)
        }
      )
    }
  }
}

class Store private(val options: Options, val cache: Term.Cache) {
  store =>

  override def toString: String = "Store(output_dir = " + output_dir.absolute + ")"


  /* directories */

  val system_output_dir: Path = Path.explode("$ISABELLE_HEAPS_SYSTEM/$ML_IDENTIFIER")
  val user_output_dir: Path = Path.explode("$ISABELLE_HEAPS/$ML_IDENTIFIER")

  def system_heaps: Boolean = options.bool("system_heaps")

  val output_dir: Path =
    if (system_heaps) system_output_dir else user_output_dir

  val input_dirs: List[Path] =
    if (system_heaps) List(system_output_dir)
    else List(user_output_dir, system_output_dir)

  def presentation_dir: Path =
    if (system_heaps) Path.explode("$ISABELLE_BROWSER_INFO_SYSTEM")
    else Path.explode("$ISABELLE_BROWSER_INFO")


  /* file names */

  def heap(name: String): Path = Path.basic(name)
  def database(name: String): Path = Path.basic("log") + Path.basic(name).db
  def log(name: String): Path = Path.basic("log") + Path.basic(name)
  def log_gz(name: String): Path = log(name).gz

  def output_heap(name: String): Path = output_dir + heap(name)
  def output_database(name: String): Path = output_dir + database(name)
  def output_log(name: String): Path = output_dir + log(name)
  def output_log_gz(name: String): Path = output_dir + log_gz(name)


  /* heap */

  def find_heap(name: String): Option[Path] =
    input_dirs.map(_ + heap(name)).find(_.is_file)

  def the_heap(name: String): Path =
    find_heap(name) getOrElse
      error("Missing heap image for session " + quote(name) + " -- expected in:\n" +
        cat_lines(input_dirs.map(dir => "  " + File.standard_path(dir))))

  def heap_shasum(database_server: Option[SQL.Database], name: String): SHA1.Shasum = {
    def get_database = database_server.flatMap(ML_Heap.get_entry(_, name))
    def get_file = find_heap(name).flatMap(ML_Heap.read_file_digest)

    get_database orElse get_file match {
      case Some(digest) => SHA1.shasum(digest, name)
      case None => SHA1.no_shasum
    }
  }


  /* databases for build process and session content */

  def find_database(name: String): Option[Path] =
    input_dirs.map(_ + database(name)).find(_.is_file)

  def build_database_server: Boolean = options.bool("build_database_server")
  def build_database_test: Boolean = options.bool("build_database_test")

  def open_database_server(): PostgreSQL.Database =
    PostgreSQL.open_database(
      user = options.string("build_database_user"),
      password = options.string("build_database_password"),
      database = options.string("build_database_name"),
      host = options.string("build_database_host"),
      port = options.int("build_database_port"),
      ssh =
        proper_string(options.string("build_database_ssh_host")).map(ssh_host =>
          SSH.open_session(options,
            host = ssh_host,
            user = options.string("build_database_ssh_user"),
            port = options.int("build_database_ssh_port"))),
      ssh_close = true)

  def maybe_open_database_server(): Option[SQL.Database] =
    if (build_database_server) Some(open_database_server()) else None

  def open_build_database(path: Path): SQL.Database =
    if (build_database_server) open_database_server()
    else SQLite.open_database(path, restrict = true)

  def maybe_open_build_database(
    path: Path = Path.explode("$ISABELLE_HOME_USER/build.db")
  ): Option[SQL.Database] = if (build_database_test) Some(open_build_database(path)) else None

  def try_open_database(
    name: String,
    output: Boolean = false,
    server: Boolean = build_database_server
  ): Option[SQL.Database] = {
    def check(db: SQL.Database): Option[SQL.Database] =
      if (output || session_info_exists(db)) Some(db) else { db.close(); None }

    if (server) check(open_database_server())
    else if (output) Some(SQLite.open_database(output_database(name)))
    else {
      (for {
        dir <- input_dirs.view
        path = dir + database(name) if path.is_file
        db <- check(SQLite.open_database(path))
      } yield db).headOption
    }
  }

  def error_database(name: String): Nothing =
    error("Missing build database for session " + quote(name))

  def open_database(name: String, output: Boolean = false): SQL.Database =
    try_open_database(name, output = output) getOrElse error_database(name)

  def clean_output(
    database_server: Option[SQL.Database],
    name: String,
    session_init: Boolean = false
  ): Option[Boolean] = {
    val relevant_db =
      database_server match {
        case Some(db) =>
          ML_Heap.clean_entry(db, name)
          clean_session_info(db, name)
        case None => false
      }

    val del =
      for {
        dir <-
          (if (system_heaps) List(user_output_dir, system_output_dir) else List(user_output_dir))
        file <- List(heap(name), database(name), log(name), log_gz(name))
        path = dir + file if path.is_file
      } yield path.file.delete

    if (database_server.isEmpty && session_init) {
      using(open_database(name, output = true))(clean_session_info(_, name))
    }

    if (relevant_db || del.nonEmpty) Some(del.forall(identity)) else None
  }

  def check_output(
    name: String,
    session_options: Options,
    sources_shasum: SHA1.Shasum,
    input_shasum: SHA1.Shasum,
    fresh_build: Boolean,
    store_heap: Boolean
  ): (Boolean, SHA1.Shasum) = {
    try_open_database(name) match {
      case Some(db) =>
        using(db) { _ =>
          read_build(db, name) match {
            case Some(build) =>
              val output_shasum = heap_shasum(if (db.is_postgresql) Some(db) else None, name)
              val current =
                !fresh_build &&
                  build.ok &&
                  Sessions.eq_sources(session_options, build.sources, sources_shasum) &&
                  build.input_heaps == input_shasum &&
                  build.output_heap == output_shasum &&
                  !(store_heap && output_shasum.is_empty)
              (current, output_shasum)
            case None => (false, SHA1.no_shasum)
          }
        }
      case None => (false, SHA1.no_shasum)
    }
  }


  /* session info */

  def session_info_exists(db: SQL.Database): Boolean = {
    val tables = db.tables
    Store.Data.tables.forall(table => tables.contains(table.name))
  }

  def session_info_defined(db: SQL.Database, name: String): Boolean =
    db.execute_query_statementB(
      Store.Data.Session_Info.table.select(List(Store.Data.Session_Info.session_name),
        sql = Store.Data.Session_Info.session_name.where_equal(name)))

  def clean_session_info(db: SQL.Database, name: String): Boolean = {
    Export.clean_session(db, name)
    Document_Build.clean_session(db, name)

    Store.Data.transaction_lock(db, create = true, synchronized = true) {
      val already_defined = session_info_defined(db, name)

      db.execute_statement(
        Store.Data.Session_Info.table.delete(
          sql = Store.Data.Session_Info.session_name.where_equal(name)))
      if (db.is_postgresql) db.execute_statement(Store.Data.Session_Info.augment_table)

      db.execute_statement(Store.Data.Sources.table.delete(
        sql = Store.Data.Sources.where_equal(name)))

      already_defined
    }
  }

  def write_session_info(
    db: SQL.Database,
    session_name: String,
    sources: Store.Sources,
    build_log: Build_Log.Session_Info,
    build: Store.Build_Info
  ): Unit = {
    Store.Data.transaction_lock(db, synchronized = true) {
      Store.Data.write_sources(db, session_name, sources)
      Store.Data.write_session_info(db, cache.compress, session_name, build_log, build)
    }
  }

  def read_session_timing(db: SQL.Database, session: String): Properties.T =
    Store.Data.transaction_lock(db) { Store.Data.read_session_timing(db, session, cache) }

  def read_command_timings(db: SQL.Database, session: String): Bytes =
    Store.Data.transaction_lock(db) { Store.Data.read_command_timings(db, session) }

  def read_theory_timings(db: SQL.Database, session: String): List[Properties.T] =
    Store.Data.transaction_lock(db) { Store.Data.read_theory_timings(db, session, cache) }

  def read_ml_statistics(db: SQL.Database, session: String): List[Properties.T] =
    Store.Data.transaction_lock(db) { Store.Data.read_ml_statistics(db, session, cache) }

  def read_task_statistics(db: SQL.Database, session: String): List[Properties.T] =
    Store.Data.transaction_lock(db) { Store.Data.read_task_statistics(db, session, cache) }

  def read_theories(db: SQL.Database, session: String): List[String] =
    read_theory_timings(db, session).flatMap(Markup.Name.unapply)

  def read_errors(db: SQL.Database, session: String): List[String] =
    Store.Data.transaction_lock(db) { Store.Data.read_errors(db, session, cache) }

  def read_build(db: SQL.Database, session: String): Option[Store.Build_Info] =
    Store.Data.transaction_lock(db) { Store.Data.read_build(db, session) }

  def read_sources(db: SQL.Database, session: String, name: String = ""): List[Store.Source_File] =
    Store.Data.transaction_lock(db) { Store.Data.read_sources(db, session, name, cache.compress) }
}
