/*  Title:      Pure/Tools/build_log.scala
    Author:     Makarius

Build log parsing for historic versions, back to "build_history_base".
*/

package isabelle


import java.time.ZonedDateTime
import java.time.format.{DateTimeFormatter, DateTimeParseException}

import scala.collection.mutable
import scala.util.matching.Regex


object Build_Log
{
  /** settings **/

  object Settings
  {
    val build_settings = List("ISABELLE_BUILD_OPTIONS")
    val ml_settings = List("ML_PLATFORM", "ML_HOME", "ML_SYSTEM", "ML_OPTIONS")
    val all_settings = build_settings ::: ml_settings

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
        build_settings.map(Entry.getenv(_)) ::: List("") ::: ml_settings.map(Entry.getenv(_)))
  }


  /** log file **/

  object Log_File
  {
    def apply(path: Path): Log_File =
    {
      val (path_name, ext) = path.expand.split_ext
      val text =
        if (ext == "gz") File.read_gzip(path)
        else if (ext == "xz") File.read_xz(path)
        else File.read(path)
      apply(path_name.base.implode, text)
    }

    def apply(name: String, lines: List[String]): Log_File =
      new Log_File(name, lines)

    def apply(name: String, text: String): Log_File =
      Log_File(name, Library.trim_split_lines(text))
  }

  class Log_File private(val name: String, val lines: List[String])
  {
    log_file =>

    override def toString: String = name

    def text: String = cat_lines(lines)

    def err(msg: String): Nothing =
      error("Error in log file " + quote(name) + ": " + msg)


    /* inlined content */

    def find[A](f: String => Option[A]): Option[A] =
      lines.iterator.map(f).find(_.isDefined).map(_.get)

    def find_match(regex: Regex): Option[String] =
      lines.iterator.map(regex.unapplySeq(_)).find(res => res.isDefined && res.get.length == 1).
        map(res => res.get.head)


    /* settings */

    def get_setting(a: String): Settings.Entry =
      Settings.Entry.unapply(
        lines.find(_.startsWith(a + "=")) getOrElse err("missing " + a)).get

    def get_settings(as: List[String]): Settings.T = as.map(get_setting(_))


    /* properties (YXML) */

    val xml_cache = new XML.Cache()

    def parse_props(text: String): Properties.T =
      xml_cache.props(XML.Decode.properties(YXML.parse_body(text)))

    def filter_props(prefix: String): List[Properties.T] =
      for (line <- lines; s <- Library.try_unprefix(prefix, line)) yield parse_props(s)

    def find_line(prefix: String): Option[String] =
      find(Library.try_unprefix(prefix, _))

    def find_props(prefix: String): Option[Properties.T] =
      find_line(prefix).map(parse_props(_))


    /* parse various formats */

    def parse_session_info(
        default_name: String = "",
        command_timings: Boolean = false,
        ml_statistics: Boolean = false,
        task_statistics: Boolean = false): Session_Info =
      Build_Log.parse_session_info(
        log_file, default_name, command_timings, ml_statistics, task_statistics)

    def parse_header(): Header = Build_Log.parse_header(log_file)

    def parse_build_info(): Build_Info = Build_Log.parse_build_info(log_file)
  }


  /* session log: produced by "isabelle build" */

  sealed case class Session_Info(
    session_name: String,
    session_timing: Properties.T,
    command_timings: List[Properties.T],
    ml_statistics: List[Properties.T],
    task_statistics: List[Properties.T])

  private def parse_session_info(
    log_file: Log_File,
    default_name: String,
    command_timings: Boolean,
    ml_statistics: Boolean,
    task_statistics: Boolean): Session_Info =
  {
    val xml_cache = new XML.Cache()

    val session_name =
      log_file.find_line("\fSession.name = ") match {
        case None => default_name
        case Some(name) if default_name == "" || default_name == name => name
        case Some(name) => log_file.err("log from different session " + quote(name))
      }
    val session_timing = log_file.find_props("\fTiming = ") getOrElse Nil
    val command_timings_ =
      if (command_timings) log_file.filter_props("\fcommand_timing = ") else Nil
    val ml_statistics_ =
      if (ml_statistics) log_file.filter_props("\fML_statistics = ") else Nil
    val task_statistics_ =
      if (task_statistics) log_file.filter_props("\ftask_statistics = ") else Nil

    Session_Info(session_name, session_timing, command_timings_, ml_statistics_, task_statistics_)
  }


  /* header and meta data */

  object Header_Kind extends Enumeration
  {
    val ISATEST = Value("isatest")
    val AFP_TEST = Value("afp-test")
    val JENKINS = Value("jenkins")
  }

  sealed case class Header(
    kind: Header_Kind.Value, props: Properties.T, settings: List[(String, String)])

  object Field
  {
    val build_host = "build_host"
    val build_start = "build_start"
    val build_end = "build_end"
    val isabelle_version = "isabelle_version"
    val afp_version = "afp_version"
  }

  object AFP
  {
    val Date_Format =
      Date.Format.make_patterns(List("EEE MMM d HH:mm:ss VV yyyy", "EEE MMM d HH:mm:ss O yyyy"),
        // workaround for jdk-8u102
        s => Word.implode(Word.explode(s).map({ case "CEST" => "GMT+2" case a => a })))

    val Test_Start = new Regex("""^Start test (?:for \S+)? at (.+), (\S+)$""")
    val Test_End = new Regex("""^End test on (.+), \S+, elapsed time:.*$""")
    val Isabelle_Version = new Regex("""^Isabelle version: .* -- hg id (\S+)$""")
    val AFP_Version = new Regex("""^AFP version: .* -- hg id (\S+)$""")
  }

  private def parse_header(log_file: Log_File): Header =
  {
    log_file.lines match {
      case AFP.Test_Start(start, hostname) :: _ =>
        (start, log_file.lines.last) match {
          case (AFP.Date_Format(start_date), AFP.Test_End(AFP.Date_Format(end_date))) =>
            val isabelle_version =
              log_file.find_match(AFP.Isabelle_Version).map((Field.isabelle_version, _))
            val afp_version =
              log_file.find_match(AFP.AFP_Version).map((Field.afp_version, _))

            Header(Header_Kind.AFP_TEST,
              List(
                Field.build_host -> hostname,
                Field.build_start -> start_date.toString,
                Field.build_end -> end_date.toString) :::
              isabelle_version.toList :::
              afp_version.toList,
              log_file.get_settings(Settings.all_settings))

          case _ => log_file.err("cannot detect start/end date in afp-test log")
        }
      case _ => log_file.err("cannot detect log header format")
    }
  }


  /* build info: produced by isabelle build */

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
    status: Session_Status.Value)
  {
    def finished: Boolean = status == Session_Status.FINISHED
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

    def finished(name: String): Boolean = get_default(name, _.finished, false)
    def timing(name: String): Timing = get_default(name, _.timing, Timing.zero)
    def ml_timing(name: String): Timing = get_default(name, _.ml_timing, Timing.zero)
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

    var chapter = Map.empty[String, String]
    var groups = Map.empty[String, List[String]]
    var threads = Map.empty[String, Int]
    var timing = Map.empty[String, Timing]
    var ml_timing = Map.empty[String, Timing]
    var started = Set.empty[String]
    var failed = Set.empty[String]
    var cancelled = Set.empty[String]
    def all_sessions: Set[String] =
      chapter.keySet ++ groups.keySet ++ threads.keySet ++
      timing.keySet ++ ml_timing.keySet ++ failed ++ cancelled ++ started


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
              status)
          (name -> entry)
        }):_*)
    Build_Info(sessions)
  }
}
