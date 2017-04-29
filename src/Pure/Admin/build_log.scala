/*  Title:      Pure/Admin/build_log.scala
    Author:     Makarius

Management of build log files and database storage.
*/

package isabelle


import java.io.{File => JFile}
import java.time.ZoneId
import java.time.format.{DateTimeFormatter, DateTimeParseException}
import java.util.Locale
import java.sql.PreparedStatement

import scala.collection.immutable.SortedMap
import scala.collection.mutable
import scala.util.matching.Regex


object Build_Log
{
  /** content **/

  /* properties */

  object Prop
  {
    val build_tags = SQL.Column.string("build_tags")  // lines
    val build_args = SQL.Column.string("build_args")  // lines
    val build_group_id = SQL.Column.string("build_group_id")
    val build_id = SQL.Column.string("build_id")
    val build_engine = SQL.Column.string("build_engine")
    val build_host = SQL.Column.string("build_host")
    val build_start = SQL.Column.date("build_start")
    val build_end = SQL.Column.date("build_end")
    val isabelle_version = SQL.Column.string("isabelle_version")
    val afp_version = SQL.Column.string("afp_version")

    val all_props: List[SQL.Column] =
      List(build_tags, build_args, build_group_id, build_id, build_engine,
        build_host, build_start, build_end, isabelle_version, afp_version)
  }


  /* settings */

  object Settings
  {
    val ISABELLE_BUILD_OPTIONS = SQL.Column.string("ISABELLE_BUILD_OPTIONS")
    val ML_PLATFORM = SQL.Column.string("ML_PLATFORM")
    val ML_HOME = SQL.Column.string("ML_HOME")
    val ML_SYSTEM = SQL.Column.string("ML_SYSTEM")
    val ML_OPTIONS = SQL.Column.string("ML_OPTIONS")

    val ml_settings = List(ML_PLATFORM, ML_HOME, ML_SYSTEM, ML_OPTIONS)
    val all_settings = ISABELLE_BUILD_OPTIONS :: ml_settings

    type Entry = (String, String)
    type T = List[Entry]

    object Entry
    {
      def unapply(s: String): Option[Entry] =
        s.indexOf('=') match {
          case -1 => None
          case i =>
            val a = s.substring(0, i)
            val b = Library.perhaps_unquote(s.substring(i + 1))
            Some((a, b))
        }
      def apply(a: String, b: String): String = a + "=" + quote(b)
      def getenv(a: String): String = apply(a, Isabelle_System.getenv(a))
    }

    def show(): String =
      cat_lines(
        List(Entry.getenv(ISABELLE_BUILD_OPTIONS.name), "") :::
        ml_settings.map(c => Entry.getenv(c.name)))
  }


  /* file names */

  def log_date(date: Date): String =
    String.format(Locale.ROOT, "%s.%05d",
      DateTimeFormatter.ofPattern("yyyy-MM-dd").format(date.rep),
      new java.lang.Long((date.time - date.midnight.time).ms / 1000))

  def log_subdir(date: Date): Path =
    Path.explode("log") + Path.explode(date.rep.getYear.toString)

  def log_filename(engine: String, date: Date, more: List[String] = Nil): Path =
    Path.explode((engine :: log_date(date) :: more).mkString("", "_", ".log"))



  /** log file **/

  def print_date(date: Date): String = Log_File.Date_Format(date)

  object Log_File
  {
    /* log file */

    def plain_name(name: String): String =
    {
      List(".log", ".log.gz", ".log.xz", ".gz", ".xz").find(name.endsWith(_)) match {
        case Some(s) => Library.try_unsuffix(s, name).get
        case None => name
      }
    }

    def apply(name: String, lines: List[String]): Log_File =
      new Log_File(plain_name(name), lines)

    def apply(name: String, text: String): Log_File =
      Log_File(name, Library.trim_split_lines(text))

    def apply(file: JFile): Log_File =
    {
      val name = file.getName
      val text =
        if (name.endsWith(".gz")) File.read_gzip(file)
        else if (name.endsWith(".xz")) File.read_xz(file)
        else File.read(file)
      apply(name, text)
    }

    def apply(path: Path): Log_File = apply(path.file)


    /* log file collections */

    def is_log(file: JFile,
      prefixes: List[String] =
        List(Build_History.log_prefix, Isatest.log_prefix, AFP_Test.log_prefix),
      suffixes: List[String] = List(".log", ".log.gz", ".log.xz")): Boolean =
    {
      val name = file.getName
      prefixes.exists(name.startsWith(_)) &&
      suffixes.exists(name.endsWith(_))
    }

    def find_files(dirs: Iterable[Path]): List[JFile] =
      dirs.iterator.flatMap(dir => File.find_files(dir.file, is_log(_))).toList


    /* date format */

    val Date_Format =
    {
      val fmts =
        Date.Formatter.variants(
          List("EEE MMM d HH:mm:ss O yyyy", "EEE MMM d HH:mm:ss VV yyyy"),
          List(Locale.ENGLISH, Locale.GERMAN)) :::
        List(
          DateTimeFormatter.RFC_1123_DATE_TIME,
          Date.Formatter.pattern("EEE MMM d HH:mm:ss yyyy").withZone(ZoneId.of("Europe/Berlin")))

      def tune_timezone(s: String): String =
        s match {
          case "CET" | "MET" => "GMT+1"
          case "CEST" | "MEST" => "GMT+2"
          case "EST" => "Europe/Berlin"
          case _ => s
        }
      def tune_weekday(s: String): String =
        s match {
          case "Die" => "Di"
          case "Mit" => "Mi"
          case "Don" => "Do"
          case "Fre" => "Fr"
          case "Sam" => "Sa"
          case "Son" => "So"
          case _ => s
        }

      def tune(s: String): String =
        Word.implode(
          Word.explode(s) match {
            case a :: "M\uFFFDr" :: bs => tune_weekday(a) :: "Mär" :: bs.map(tune_timezone(_))
            case a :: bs => tune_weekday(a) :: bs.map(tune_timezone(_))
            case Nil => Nil
          }
        )

      Date.Format.make(fmts, tune)
    }


    /* inlined content */

    def print_props(marker: String, props: Properties.T): String =
      marker + YXML.string_of_body(XML.Encode.properties(Properties.encode_lines(props)))
  }

  class Log_File private(val name: String, val lines: List[String])
  {
    log_file =>

    override def toString: String = name

    def text: String = cat_lines(lines)

    def err(msg: String): Nothing =
      error("Error in log file " + quote(name) + ": " + msg)


    /* date format */

    object Strict_Date
    {
      def unapply(s: String): Some[Date] =
        try { Some(Log_File.Date_Format.parse(s)) }
        catch { case exn: DateTimeParseException => log_file.err(exn.getMessage) }
    }


    /* inlined content */

    def find[A](f: String => Option[A]): Option[A] =
      lines.iterator.map(f).find(_.isDefined).map(_.get)

    def find_line(marker: String): Option[String] =
      find(Library.try_unprefix(marker, _))

    def find_match(regex: Regex): Option[String] =
      lines.iterator.map(regex.unapplySeq(_)).find(res => res.isDefined && res.get.length == 1).
        map(res => res.get.head)


    /* settings */

    def get_setting(a: String): Option[Settings.Entry] =
      lines.find(_.startsWith(a + "=")) match {
        case Some(line) => Settings.Entry.unapply(line)
        case None => None
      }

    def get_all_settings: Settings.T =
      for { c <- Settings.all_settings; entry <- get_setting(c.name) }
      yield entry


    /* properties (YXML) */

    val xml_cache = new XML.Cache()

    def parse_props(text: String): Properties.T =
      xml_cache.props(Properties.decode_lines(XML.Decode.properties(YXML.parse_body(text))))

    def filter_props(marker: String): List[Properties.T] =
      for {
        line <- lines
        s <- Library.try_unprefix(marker, line)
        if YXML.detect(s)
      } yield parse_props(s)

    def find_props(marker: String): Option[Properties.T] =
      find_line(marker) match {
        case Some(text) if YXML.detect(text) => Some(parse_props(text))
        case _ => None
      }


    /* parse various formats */

    def parse_meta_info(): Meta_Info = Build_Log.parse_meta_info(log_file)

    def parse_build_info(): Build_Info = Build_Log.parse_build_info(log_file)

    def parse_session_info(
        command_timings: Boolean = false,
        ml_statistics: Boolean = false,
        task_statistics: Boolean = false): Session_Info =
      Build_Log.parse_session_info(log_file, command_timings, ml_statistics, task_statistics)
  }



  /** digested meta info: produced by Admin/build_history in log.xz file **/

  object Meta_Info
  {
    val empty: Meta_Info = Meta_Info(Nil, Nil)

    val log_name = SQL.Column.string("log_name", primary_key = true)
    val table =
      SQL.Table("isabelle_build_log_meta_info", log_name :: Prop.all_props ::: Settings.all_settings)
  }

  sealed case class Meta_Info(props: Properties.T, settings: Settings.T)
  {
    def is_empty: Boolean = props.isEmpty && settings.isEmpty

    def get(c: SQL.Column): Option[String] =
      Properties.get(props, c.name) orElse
      Properties.get(settings, c.name)

    def get_date(c: SQL.Column): Option[Date] =
      get(c).map(Log_File.Date_Format.parse(_))
  }

  object Isatest
  {
    val log_prefix = "isatest-makeall-"
    val engine = "isatest"
    val Start = new Regex("""^------------------- starting test --- (.+) --- (.+)$""")
    val End = new Regex("""^------------------- test (?:successful|FAILED) --- (.+) --- .*$""")
    val Isabelle_Version = new Regex("""^Isabelle version: (\S+)$""")
    val No_AFP_Version = new Regex("""$.""")
  }

  object AFP_Test
  {
    val log_prefix = "afp-test-devel-"
    val engine = "afp-test"
    val Start = new Regex("""^Start test(?: for .+)? at ([^,]+), (.*)$""")
    val Start_Old = new Regex("""^Start test(?: for .+)? at ([^,]+)$""")
    val End = new Regex("""^End test on (.+), .+, elapsed time:.*$""")
    val Isabelle_Version = new Regex("""^Isabelle version: .* -- hg id (\S+)$""")
    val AFP_Version = new Regex("""^AFP version: .* -- hg id (\S+)$""")
    val Bad_Init = new Regex("""^cp:.*: Disc quota exceeded$""")
  }

  object Jenkins
  {
    val engine = "jenkins"
    val Start = new Regex("""^Started .*$""")
    val Start_Date = new Regex("""^Build started at (.+)$""")
    val No_End = new Regex("""$.""")
    val Isabelle_Version = new Regex("""^Isabelle id (\S+)$""")
    val AFP_Version = new Regex("""^AFP id (\S+)$""")
    val CONFIGURATION = "=== CONFIGURATION ==="
    val BUILD = "=== BUILD ==="
    val FINISHED = "Finished: "
  }

  private def parse_meta_info(log_file: Log_File): Meta_Info =
  {
    def parse(engine: String, host: String, start: Date,
      End: Regex, Isabelle_Version: Regex, AFP_Version: Regex): Meta_Info =
    {
      val build_id =
      {
        val prefix = if (host != "") host else if (engine != "") engine else ""
        (if (prefix == "") "build" else prefix) + ":" + start.time.ms
      }
      val build_engine = if (engine == "") Nil else List(Prop.build_engine.name -> engine)
      val build_host = if (host == "") Nil else List(Prop.build_host.name -> host)

      val start_date = List(Prop.build_start.name -> print_date(start))
      val end_date =
        log_file.lines.last match {
          case End(log_file.Strict_Date(end_date)) =>
            List(Prop.build_end.name -> print_date(end_date))
          case _ => Nil
        }

      val isabelle_version =
        log_file.find_match(Isabelle_Version).map(Prop.isabelle_version.name -> _)
      val afp_version =
        log_file.find_match(AFP_Version).map(Prop.afp_version.name -> _)

      Meta_Info((Prop.build_id.name -> build_id) :: build_engine ::: build_host :::
          start_date ::: end_date ::: isabelle_version.toList ::: afp_version.toList,
        log_file.get_all_settings)
    }

    log_file.lines match {
      case line :: _ if line.startsWith(Build_History.META_INFO_MARKER) =>
        Meta_Info(log_file.find_props(Build_History.META_INFO_MARKER).get,
          log_file.get_all_settings)

      case Isatest.Start(log_file.Strict_Date(start), host) :: _ =>
        parse(Isatest.engine, host, start, Isatest.End,
          Isatest.Isabelle_Version, Isatest.No_AFP_Version)

      case AFP_Test.Start(log_file.Strict_Date(start), host) :: _ =>
        parse(AFP_Test.engine, host, start, AFP_Test.End,
          AFP_Test.Isabelle_Version, AFP_Test.AFP_Version)

      case AFP_Test.Start_Old(log_file.Strict_Date(start)) :: _ =>
        parse(AFP_Test.engine, "", start, AFP_Test.End,
          AFP_Test.Isabelle_Version, AFP_Test.AFP_Version)

      case Jenkins.Start() :: _
      if log_file.lines.contains(Jenkins.CONFIGURATION) ||
         log_file.lines.last.startsWith(Jenkins.FINISHED) =>
        log_file.lines.dropWhile(_ != Jenkins.BUILD) match {
          case Jenkins.BUILD :: _ :: Jenkins.Start_Date(log_file.Strict_Date(start)) :: _ =>
            parse(Jenkins.engine, "", start.to(ZoneId.of("Europe/Berlin")), Jenkins.No_End,
              Jenkins.Isabelle_Version, Jenkins.AFP_Version)
          case _ => Meta_Info.empty
        }

      case line :: _ if line.startsWith("\u0000") => Meta_Info.empty
      case List(Isatest.End(_)) => Meta_Info.empty
      case _ :: AFP_Test.Bad_Init() :: _ => Meta_Info.empty
      case Nil => Meta_Info.empty

      case _ => log_file.err("cannot detect log file format")
    }
  }



  /** build info: toplevel output of isabelle build or Admin/build_history **/

  val ML_STATISTICS_MARKER = "\fML_statistics = "
  val SESSION_NAME = "session_name"

  object Session_Status extends Enumeration
  {
    val EXISTING = Value("existing")
    val FINISHED = Value("finished")
    val FAILED = Value("failed")
    val CANCELLED = Value("cancelled")
  }

  sealed case class Session_Entry(
    chapter: String,
    groups: List[String],
    threads: Option[Int],
    timing: Timing,
    ml_timing: Timing,
    ml_statistics: List[Properties.T],
    heap_size: Option[Long],
    status: Session_Status.Value)
  {
    def finished: Boolean = status == Session_Status.FINISHED
  }

  object Build_Info
  {
    val session_name = SQL.Column.string("session_name", primary_key = true)
    val chapter = SQL.Column.string("chapter")
    val groups = SQL.Column.string("groups")
    val threads = SQL.Column.int("threads")
    val timing_elapsed = SQL.Column.long("timing_elapsed")
    val timing_cpu = SQL.Column.long("timing_cpu")
    val timing_gc = SQL.Column.long("timing_gc")
    val ml_timing_elapsed = SQL.Column.long("ml_timing_elapsed")
    val ml_timing_cpu = SQL.Column.long("ml_timing_cpu")
    val ml_timing_gc = SQL.Column.long("ml_timing_gc")
    val ml_statistics = SQL.Column.bytes("ml_statistics")
    val heap_size = SQL.Column.long("heap_size")
    val status = SQL.Column.string("status")

    val table = SQL.Table("isabelle_build_log_build_info",
      List(Meta_Info.log_name, session_name, chapter, groups, threads, timing_elapsed, timing_cpu,
        timing_gc, ml_timing_elapsed, ml_timing_cpu, ml_timing_gc, ml_statistics, heap_size, status))

    val table0 = table.copy(columns = table.columns.take(2))
  }

  sealed case class Build_Info(sessions: Map[String, Session_Entry])
  {
    def session(name: String): Session_Entry = sessions(name)
    def get_session(name: String): Option[Session_Entry] = sessions.get(name)

    def get_default[A](name: String, f: Session_Entry => A, x: A): A =
      get_session(name) match {
        case Some(entry) => f(entry)
        case None => x
      }

    def finished_sessions: List[String] = sessions.keySet.iterator.filter(finished(_)).toList
    def finished(name: String): Boolean = get_default(name, _.finished, false)
    def timing(name: String): Timing = get_default(name, _.timing, Timing.zero)
    def ml_timing(name: String): Timing = get_default(name, _.ml_timing, Timing.zero)
    def ml_statistics(name: String): ML_Statistics =
      get_default(name, entry => ML_Statistics(name, entry.ml_statistics), ML_Statistics.empty)
  }

  private def parse_build_info(log_file: Log_File): Build_Info =
  {
    object Chapter_Name
    {
      def unapply(s: String): Some[(String, String)] =
        space_explode('/', s) match {
          case List(chapter, name) => Some((chapter, name))
          case _ => Some(("", s))
        }
    }

    val Session_No_Groups = new Regex("""^Session (\S+)$""")
    val Session_Groups = new Regex("""^Session (\S+) \((.*)\)$""")
    val Session_Finished1 =
      new Regex("""^Finished (\S+) \((\d+):(\d+):(\d+) elapsed time, (\d+):(\d+):(\d+) cpu time.*$""")
    val Session_Finished2 =
      new Regex("""^Finished (\S+) \((\d+):(\d+):(\d+) elapsed time.*$""")
    val Session_Timing =
      new Regex("""^Timing (\S+) \((\d) threads, (\d+\.\d+)s elapsed time, (\d+\.\d+)s cpu time, (\d+\.\d+)s GC time.*$""")
    val Session_Started = new Regex("""^(?:Running|Building) (\S+) \.\.\.$""")
    val Session_Failed = new Regex("""^(\S+) FAILED""")
    val Session_Cancelled = new Regex("""^(\S+) CANCELLED""")
    val Heap = new Regex("""^Heap (\S+) \((\d+) bytes\)$""")

    var chapter = Map.empty[String, String]
    var groups = Map.empty[String, List[String]]
    var threads = Map.empty[String, Int]
    var timing = Map.empty[String, Timing]
    var ml_timing = Map.empty[String, Timing]
    var started = Set.empty[String]
    var failed = Set.empty[String]
    var cancelled = Set.empty[String]
    var ml_statistics = Map.empty[String, List[Properties.T]]
    var heap_sizes = Map.empty[String, Long]

    def all_sessions: Set[String] =
      chapter.keySet ++ groups.keySet ++ threads.keySet ++ timing.keySet ++ ml_timing.keySet ++
      failed ++ cancelled ++ started ++ ml_statistics.keySet ++ heap_sizes.keySet


    for (line <- log_file.lines) {
      line match {
        case Session_No_Groups(Chapter_Name(chapt, name)) =>
          chapter += (name -> chapt)
          groups += (name -> Nil)

        case Session_Groups(Chapter_Name(chapt, name), grps) =>
          chapter += (name -> chapt)
          groups += (name -> Word.explode(grps))

        case Session_Started(name) =>
          started += name

        case Session_Finished1(name,
            Value.Int(e1), Value.Int(e2), Value.Int(e3),
            Value.Int(c1), Value.Int(c2), Value.Int(c3)) =>
          val elapsed = Time.hms(e1, e2, e3)
          val cpu = Time.hms(c1, c2, c3)
          timing += (name -> Timing(elapsed, cpu, Time.zero))

        case Session_Finished2(name,
            Value.Int(e1), Value.Int(e2), Value.Int(e3)) =>
          val elapsed = Time.hms(e1, e2, e3)
          timing += (name -> Timing(elapsed, Time.zero, Time.zero))

        case Session_Timing(name,
            Value.Int(t), Value.Double(e), Value.Double(c), Value.Double(g)) =>
          val elapsed = Time.seconds(e)
          val cpu = Time.seconds(c)
          val gc = Time.seconds(g)
          ml_timing += (name -> Timing(elapsed, cpu, gc))
          threads += (name -> t)

        case Heap(name, Value.Long(size)) =>
          heap_sizes += (name -> size)

        case _ if line.startsWith(ML_STATISTICS_MARKER) && YXML.detect(line) =>
          val (name, props) =
            Library.try_unprefix(ML_STATISTICS_MARKER, line).map(log_file.parse_props(_)) match {
              case Some((SESSION_NAME, session_name) :: props) => (session_name, props)
              case _ => log_file.err("malformed ML_statistics " + quote(line))
            }
          ml_statistics += (name -> (props :: ml_statistics.getOrElse(name, Nil)))

        case _ =>
      }
    }

    val sessions =
      Map(
        (for (name <- all_sessions.toList) yield {
          val status =
            if (failed(name)) Session_Status.FAILED
            else if (cancelled(name)) Session_Status.CANCELLED
            else if (timing.isDefinedAt(name) || ml_timing.isDefinedAt(name))
              Session_Status.FINISHED
            else if (started(name)) Session_Status.FAILED
            else Session_Status.EXISTING
          val entry =
            Session_Entry(
              chapter.getOrElse(name, ""),
              groups.getOrElse(name, Nil),
              threads.get(name),
              timing.getOrElse(name, Timing.zero),
              ml_timing.getOrElse(name, Timing.zero),
              ml_statistics.getOrElse(name, Nil).reverse,
              heap_sizes.get(name),
              status)
          (name -> entry)
        }):_*)
    Build_Info(sessions)
  }



  /** session info: produced by isabelle build as session log.gz file **/

  sealed case class Session_Info(
    session_timing: Properties.T,
    command_timings: List[Properties.T],
    ml_statistics: List[Properties.T],
    task_statistics: List[Properties.T])

  private def parse_session_info(
    log_file: Log_File,
    command_timings: Boolean,
    ml_statistics: Boolean,
    task_statistics: Boolean): Session_Info =
  {
    Session_Info(
      session_timing = log_file.find_props("\fTiming = ") getOrElse Nil,
      command_timings = if (command_timings) log_file.filter_props("\fcommand_timing = ") else Nil,
      ml_statistics = if (ml_statistics) log_file.filter_props(ML_STATISTICS_MARKER) else Nil,
      task_statistics = if (task_statistics) log_file.filter_props("\ftask_statistics = ") else Nil)
  }



  /** persistent store **/

  def store(options: Options): Store = new Store(options)

  class Store private[Build_Log](options: Options) extends Properties.Store
  {
    def open_database(
      user: String = options.string("build_log_database_user"),
      password: String = options.string("build_log_database_password"),
      database: String = options.string("build_log_database_name"),
      host: String = options.string("build_log_database_host"),
      port: Int = options.int("build_log_database_port"),
      ssh_host: String = options.string("build_log_ssh_host"),
      ssh_user: String = options.string("build_log_ssh_user"),
      ssh_port: Int = options.int("build_log_ssh_port")): PostgreSQL.Database =
    {
      PostgreSQL.open_database(
        user = user, password = password, database = database, host = host, port = port,
        ssh =
          if (ssh_host == "") None
          else Some(SSH.init_context(options).open_session(ssh_host, ssh_user, port)))
    }

    def filter_files(db: SQL.Database, table: SQL.Table, files: List[JFile]): List[JFile] =
    {
      db.transaction {
        db.create_table(table)

        val key = Meta_Info.log_name
        val known_files =
          using(db.select(table, List(key), distinct = true))(stmt =>
            SQL.iterator(stmt.executeQuery)(rs => db.string(rs, key)).toSet)

        val unique_files =
          (Map.empty[String, JFile] /: files.iterator)({ case (m, file) =>
            val name = Log_File.plain_name(file.getName)
            if (known_files(name)) m else m + (name -> file)
          })

        unique_files.iterator.map(_._2).toList
      }
    }

    def write_meta_info(db: SQL.Database, files: List[JFile])
    {
      for (file_group <- filter_files(db, Meta_Info.table, files).grouped(1000)) {
        db.transaction {
          for (file <- file_group) {
            val log_file = Log_File(file)
            val meta_info = log_file.parse_meta_info()

            using(db.delete(Meta_Info.table, Meta_Info.log_name.sql_where_equal(log_file.name)))(
              _.execute)
            using(db.insert(Meta_Info.table))(stmt =>
            {
              db.set_string(stmt, 1, log_file.name)
              for ((c, i) <- Meta_Info.table.columns.tail.zipWithIndex) {
                if (c.T == SQL.Type.Date)
                  db.set_date(stmt, i + 2, meta_info.get_date(c))
                else
                  db.set_string(stmt, i + 2, meta_info.get(c))
              }
              stmt.execute()
            })
          }
        }
      }
    }

    def read_meta_info(db: SQL.Database, log_name: String): Option[Meta_Info] =
    {
      val cs = Meta_Info.table.columns.tail
      using(db.select(Meta_Info.table, cs, Meta_Info.log_name.sql_where_equal(log_name)))(stmt =>
      {
        val rs = stmt.executeQuery
        if (!rs.next) None
        else {
          val results =
            cs.map(c => c.name ->
              (if (c.T == SQL.Type.Date)
                db.get(rs, c, db.date _).map(Log_File.Date_Format(_))
               else
                db.get(rs, c, db.string _)))
          val n = Prop.all_props.length
          val props = for ((x, Some(y)) <- results.take(n)) yield (x, y)
          val settings = for ((x, Some(y)) <- results.drop(n)) yield (x, y)
          Some(Meta_Info(props, settings))
        }
      })
    }

    def write_build_info(db: SQL.Database, files: List[JFile])
    {
      for (file_group <- filter_files(db, Build_Info.table, files).grouped(100)) {
        db.transaction {
          for (file <- file_group) {
            val log_file = Log_File(file)
            val build_info = log_file.parse_build_info()

            using(db.delete(Build_Info.table, Meta_Info.log_name.sql_where_equal(log_file.name)))(
              _.execute)
            if (build_info.sessions.isEmpty) {
              using(db.insert(Build_Info.table0))(stmt =>
              {
                db.set_string(stmt, 1, log_file.name)
                db.set_string(stmt, 2, "")
                stmt.execute()
              })
            }
            else {
              using(db.insert(Build_Info.table))(stmt =>
              {
                for ((session_name, session) <- build_info.sessions.iterator) {
                  db.set_string(stmt, 1, log_file.name)
                  db.set_string(stmt, 2, session_name)
                  db.set_string(stmt, 3, session.chapter)
                  db.set_string(stmt, 4, cat_lines(session.groups))
                  db.set_int(stmt, 5, session.threads)
                  db.set_long(stmt, 6, session.timing.elapsed.proper_ms)
                  db.set_long(stmt, 7, session.timing.cpu.proper_ms)
                  db.set_long(stmt, 8, session.timing.gc.proper_ms)
                  db.set_long(stmt, 9, session.ml_timing.elapsed.proper_ms)
                  db.set_long(stmt, 10, session.ml_timing.cpu.proper_ms)
                  db.set_long(stmt, 11, session.ml_timing.gc.proper_ms)
                  db.set_bytes(stmt, 12, compress_properties(session.ml_statistics))
                  db.set_long(stmt, 13, session.heap_size)
                  db.set_string(stmt, 14, session.status.toString)
                  stmt.execute()
                }
              })
            }
          }
        }
      }
    }

    def read_build_info(
      db: SQL.Database, log_name: String, session_names: List[String] = Nil): Build_Info =
    {
      val where0 =
        Meta_Info.log_name.sql_where_equal(log_name) + " AND "
          Build_Info.session_name.sql_name + " <> ''"
      val where =
        if (session_names.isEmpty) where0
        else
          where0 + " AND " +
          session_names.map(a => Build_Info.session_name.sql_name + " = " + SQL.quote_string(a)).
            mkString("(", " OR ", ")")
      val sessions =
        using(db.select(Build_Info.table, Build_Info.table.columns.tail, where))(stmt =>
        {
          SQL.iterator(stmt.executeQuery)(rs =>
          {
            val session_name = db.string(rs, Build_Info.session_name)
            val chapter = db.string(rs, Build_Info.chapter)
            val groups = split_lines(db.string(rs, Build_Info.groups))
            val threads = db.get(rs, Build_Info.threads, db.int _)
            val timing_elapsed = Time.ms(db.long(rs, Build_Info.timing_elapsed))
            val timing_cpu = Time.ms(db.long(rs, Build_Info.timing_cpu))
            val timing_gc = Time.ms(db.long(rs, Build_Info.timing_gc))
            val ml_timing_elapsed = Time.ms(db.long(rs, Build_Info.ml_timing_elapsed))
            val ml_timing_cpu = Time.ms(db.long(rs, Build_Info.ml_timing_cpu))
            val ml_timing_gc = Time.ms(db.long(rs, Build_Info.ml_timing_gc))
            val ml_statistics = uncompress_properties(db.bytes(rs, Build_Info.ml_statistics))
            val heap_size = db.get(rs, Build_Info.heap_size, db.long _)
            val status = Session_Status.withName(db.string(rs, Build_Info.status))

            session_name ->
              Session_Entry(chapter, groups, threads, Timing(timing_elapsed, timing_cpu, timing_gc),
                Timing(ml_timing_elapsed, ml_timing_cpu, ml_timing_gc), ml_statistics,
                heap_size, status)
          }).toMap
        })
      Build_Info(sessions)
    }
  }
}
