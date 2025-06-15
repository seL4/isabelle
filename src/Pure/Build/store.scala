/*  Title:      Pure/Build/store.scala
    Author:     Makarius

Persistent store for session content: within file-system and/or SQL database.
*/

package isabelle


import java.sql.SQLException


object Store {
  def apply(
    options: Options,
    build_cluster: Boolean = false,
    cache: Term.Cache = Term.Cache.make()
  ): Store = new Store(options, build_cluster, cache)


  /* file names */

  def heap(name: String): Path = Path.basic(name)
  def log(name: String): Path = Path.basic("log") + Path.basic(name)
  def log_db(name: String): Path = log(name).db
  def log_gz(name: String): Path = log(name).gz


  /* session */

  final class Session private[Store](
    val name: String,
    val heap: Option[Path],
    val log_db: Option[Path],
    dirs: List[Path]
  ) {
    def log_db_name: String = Store.log_db(name).implode

    def defined: Boolean = heap.isDefined || log_db.isDefined

    def the_heap: Path =
      heap getOrElse
        error("Missing heap image for session " + quote(name) + " -- expected in:\n" +
          cat_lines(dirs.map(dir => "  " + File.standard_path(dir))))

    def heap_digest(): Option[SHA1.Digest] =
      heap.flatMap(ML_Heap.read_file_digest)

    override def toString: String = name
  }



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
            def err(): Nothing = error("Incoherent digest for source file: " + path.expand)
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

  object private_data extends SQL.Data() {
    override lazy val tables: SQL.Tables = SQL.Tables(Session_Info.table, Sources.table)

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

    def read_build(db: SQL.Database, name: String): Option[Store.Build_Info] =
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
        })

    def read_build_uuid(db: SQL.Database, name: String): String =
      db.execute_query_statementO[String](
        Session_Info.table.select(List(Session_Info.uuid),
          sql = Session_Info.session_name.where_equal(name)),
        { res =>
            try { Option(res.string(Session_Info.uuid)).getOrElse("") }
            catch { case _: SQLException => "" }
        }).getOrElse("")

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

    def write_sources(
      db: SQL.Database,
      session_name: String,
      source_files: Iterable[Source_File]
    ): Unit = {
      db.execute_batch_statement(Sources.table.insert(), batch =
        for (source_file <- source_files) yield { (stmt: SQL.Statement) =>
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

  def read_build_uuid(path: Path, session: String): String =
    try { using(SQLite.open_database(path))(private_data.read_build_uuid(_, session)) }
    catch { case _: SQLException => "" }
}

class Store private(
    val options: Options,
    val build_cluster: Boolean,
    val cache: Term.Cache
  ) {
  store =>

  override def toString: String = "Store(output_dir = " + output_dir.absolute + ")"


  /* ML system settings */

  val ml_settings: ML_Settings = ML_Settings.system()

  val system_output_dir: Path =
    Path.variable("ISABELLE_HEAPS_SYSTEM") + Path.basic(ml_settings.ml_identifier)

  val user_output_dir: Path =
    Path.variable("ISABELLE_HEAPS") + Path.basic(ml_settings.ml_identifier)


  /* directories */

  def system_heaps: Boolean = options.bool("system_heaps")

  val output_dir: Path =
    if (system_heaps) system_output_dir else user_output_dir

  val input_dirs: List[Path] =
    if (system_heaps) List(system_output_dir)
    else List(user_output_dir, system_output_dir)

  val clean_dirs: List[Path] =
    if (system_heaps) List(user_output_dir, system_output_dir)
    else List(user_output_dir)

  def presentation_dir: Path =
    if (system_heaps) Path.explode("$ISABELLE_BROWSER_INFO_SYSTEM")
    else Path.explode("$ISABELLE_BROWSER_INFO")


  /* file names */

  def output_heap(name: String): Path = output_dir + Store.heap(name)
  def output_log(name: String): Path = output_dir + Store.log(name)
  def output_log_db(name: String): Path = output_dir + Store.log_db(name)
  def output_log_gz(name: String): Path = output_dir + Store.log_gz(name)


  /* session */

  def get_session(name: String): Store.Session = {
    val heap = input_dirs.view.map(_ + Store.heap(name)).find(_.is_file)
    val log_db = input_dirs.view.map(_ + Store.log_db(name)).find(_.is_file)
    new Store.Session(name, heap, log_db, input_dirs)
  }

  def output_session(name: String, store_heap: Boolean = false): Store.Session = {
    val heap = if (store_heap) Some(output_heap(name)) else None
    val log_db = if (!build_database_server) Some(output_log_db(name)) else None
    new Store.Session(name, heap, log_db, List(output_dir))
  }


  /* heap */

  def heap_shasum(database_server: Option[SQL.Database], name: String): SHA1.Shasum = {
    def get_database: Option[SHA1.Digest] = {
      for {
        db <- database_server
        digest <- ML_Heap.read_digests(db, List(name)).valuesIterator.nextOption()
      } yield digest
    }

    get_database orElse get_session(name).heap_digest() match {
      case Some(digest) => SHA1.shasum(digest, name)
      case None => SHA1.no_shasum
    }
  }


  /* databases for build process and session content */

  def build_database_server: Boolean = options.bool("build_database_server")
  def build_database: Boolean = options.bool("build_database")

  def open_server(): SSH.Server =
    PostgreSQL.open_server(options,
      host = options.string("build_database_host"),
      port = options.int("build_database_port"),
      ssh_host = options.string("build_database_ssh_host"),
      ssh_port = options.int("build_database_ssh_port"),
      ssh_user = options.string("build_database_ssh_user"))

  def open_database_server(server: SSH.Server = SSH.no_server): PostgreSQL.Database =
    PostgreSQL.open_database_server(options, server = server,
      user = options.string("build_database_user"),
      password = options.string("build_database_password"),
      database = options.string("build_database_name"),
      host = options.string("build_database_host"),
      port = options.int("build_database_port"),
      ssh_host = options.string("build_database_ssh_host"),
      ssh_port = options.int("build_database_ssh_port"),
      ssh_user = options.string("build_database_ssh_user"))

  def maybe_open_database_server(
    server: SSH.Server = SSH.no_server,
    guard: Boolean = build_database_server
  ): Option[SQL.Database] = {
    if (guard) Some(open_database_server(server = server)) else None
  }

  def maybe_open_heaps_database(
    database_server: Option[SQL.Database],
    server: SSH.Server = SSH.no_server
  ): Option[SQL.Database] = {
    if (database_server.isDefined) None
    else maybe_open_database_server(server = server, guard = build_cluster)
  }

  def maybe_using_heaps_database[A](
    database_server: Option[SQL.Database],
    server: SSH.Server = SSH.no_server
  )(f: SQL.Database => A): Option[A] = {
    using_optional(maybe_open_heaps_database(database_server, server = server)) {
      heaps_database => (database_server orElse heaps_database).map(f)
    }
  }

  def in_heaps_database(
    sessions: List[Store.Session],
    database_server: Option[SQL.Database],
    server: SSH.Server = SSH.no_server,
    progress: Progress = new Progress
  ): Unit = {
    if (sessions.nonEmpty) {
      maybe_using_heaps_database(database_server, server = server) { db =>
        val slice = Space.MiB(options.real("build_database_slice"))
        sessions.foreach(ML_Heap.store(db, _, slice, cache = cache.compress, progress = progress))
      }
    }
  }

  def open_build_database(path: Path, server: SSH.Server = SSH.no_server): SQL.Database =
    if (build_database_server || build_cluster) open_database_server(server = server)
    else SQLite.open_database(path, restrict = true)

  def maybe_open_build_database(
    path: Path = Path.explode("$ISABELLE_HOME_USER/build.db"),
    server: SSH.Server = SSH.no_server
  ): Option[SQL.Database] = {
    if (build_database) Some(open_build_database(path, server = server)) else None
  }

  def try_open_database(
    name: String,
    output: Boolean = false,
    server: SSH.Server = SSH.no_server,
    server_mode: Boolean = build_database_server
  ): Option[SQL.Database] = {
    def check(db: SQL.Database): Option[SQL.Database] =
      if (output || session_info_exists(db)) Some(db) else { db.close(); None }

    if (server_mode) check(open_database_server(server = server))
    else if (output) Some(SQLite.open_database(output_log_db(name)))
    else {
      (for {
        dir <- input_dirs.view
        path = dir + Store.log_db(name) if path.is_file
        db <- check(SQLite.open_database(path))
      } yield db).headOption
    }
  }

  def error_database(name: String): Nothing =
    error("Missing build database for session " + quote(name))

  def open_database(
    name: String,
    output: Boolean = false,
    server: SSH.Server = SSH.no_server
  ): SQL.Database = {
    try_open_database(name, output = output, server = server) getOrElse error_database(name)
  }

  def clean_output(
    database_server: Option[SQL.Database],
    name: String,
    session_init: Boolean = false,
    progress: Progress = new Progress
  ): Unit = {
    val relevant_db =
      database_server match {
        case Some(db) =>
          ML_Heap.clean_entry(db, name)
          clean_session_info(db, name)
        case None => false
      }

    val del =
      for {
        dir <- clean_dirs
        file <- List(Store.heap(name), Store.log_db(name), Store.log(name), Store.log_gz(name))
        path = dir + file if path.is_file
      } yield path.file.delete

    if (database_server.isEmpty && session_init) {
      using(open_database(name, output = true))(clean_session_info(_, name))
    }

    if (relevant_db || del.nonEmpty) {
      if (del.forall(identity)) progress.echo("Cleaned " + name)
      else progress.echo(name + " FAILED to clean")
    }
  }

  def check_output(
    database_server: Option[SQL.Database],
    name: String,
    sources_shasum: SHA1.Shasum,
    input_shasum: SHA1.Shasum,
    build_thorough: Boolean = false,
    fresh_build: Boolean = false,
    store_heap: Boolean = false
  ): (Boolean, SHA1.Shasum) = {
    def no_check: (Boolean, SHA1.Shasum) = (false, SHA1.no_shasum)

    def check(db: SQL.Database): (Boolean, SHA1.Shasum) =
      read_build(db, name) match {
        case Some(build) =>
          val output_shasum = heap_shasum(if (db.is_postgresql) Some(db) else None, name)
          val current =
            !fresh_build &&
              build.ok &&
              Sessions.eq_sources(build_thorough, build.sources, sources_shasum) &&
              build.input_heaps == input_shasum &&
              build.output_heap == output_shasum &&
              !(store_heap && output_shasum.is_empty)
          (current, output_shasum)
        case None => no_check
      }

    database_server match {
      case Some(db) => if (session_info_exists(db)) check(db) else no_check
      case None => using_option(try_open_database(name))(check) getOrElse no_check
    }
  }


  /* session info */

  def session_info_exists(db: SQL.Database): Boolean =
    Store.private_data.tables.forall(db.exists_table)

  def session_info_defined(db: SQL.Database, name: String): Boolean =
    db.execute_query_statementB(
      Store.private_data.Session_Info.table.select(List(Store.private_data.Session_Info.session_name),
        sql = Store.private_data.Session_Info.session_name.where_equal(name)))

  def clean_session_info(db: SQL.Database, name: String): Boolean = {
    Export.clean_session(db, name)
    Document_Build.clean_session(db, name)

    Store.private_data.transaction_lock(db, create = true, label = "Store.clean_session_info") {
      val already_defined = session_info_defined(db, name)

      db.execute_statement(
        SQL.multi(
          Store.private_data.Session_Info.table.delete(
            sql = Store.private_data.Session_Info.session_name.where_equal(name)),
          Store.private_data.Sources.table.delete(
            sql = Store.private_data.Sources.where_equal(name))))

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
    Store.private_data.transaction_lock(db, label = "Store.write_session_info") {
      for (source_files <- sources.iterator.toList.grouped(200)) {
        Store.private_data.write_sources(db, session_name, source_files)
      }
      Store.private_data.write_session_info(db, cache.compress, session_name, build_log, build)
    }
  }

  def read_session_timing(db: SQL.Database, session: String): Properties.T =
    Store.private_data.transaction_lock(db, label = "Store.read_session_timing") {
      Store.private_data.read_session_timing(db, session, cache)
    }

  def read_command_timings(db: SQL.Database, session: String): Bytes =
    Store.private_data.transaction_lock(db, label = "Store.read_command_timings") {
      Store.private_data.read_command_timings(db, session)
    }

  def read_theory_timings(db: SQL.Database, session: String): List[Properties.T] =
    Store.private_data.transaction_lock(db, label = "Store.read_theory_timings") {
      Store.private_data.read_theory_timings(db, session, cache)
    }

  def read_ml_statistics(db: SQL.Database, session: String): List[Properties.T] =
    Store.private_data.transaction_lock(db, label = "Store.read_ml_statistics") {
      Store.private_data.read_ml_statistics(db, session, cache)
    }

  def read_task_statistics(db: SQL.Database, session: String): List[Properties.T] =
    Store.private_data.transaction_lock(db, label = "Store.read_task_statistics") {
      Store.private_data.read_task_statistics(db, session, cache)
    }

  def read_theories(db: SQL.Database, session: String): List[String] =
    read_theory_timings(db, session).flatMap(Markup.Name.unapply)

  def read_errors(db: SQL.Database, session: String): List[String] =
    Store.private_data.transaction_lock(db, label = "Store.read_errors") {
      Store.private_data.read_errors(db, session, cache)
    }

  def read_build(db: SQL.Database, session: String): Option[Store.Build_Info] =
    Store.private_data.transaction_lock(db, label = "Store.read_build") {
      if (session_info_exists(db)) Store.private_data.read_build(db, session) else None
    }

  def read_sources(db: SQL.Database, session: String, name: String = ""): List[Store.Source_File] =
    Store.private_data.transaction_lock(db, label = "Store.read_sources") {
      Store.private_data.read_sources(db, session, name, cache.compress)
    }
}
