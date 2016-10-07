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

    def parse_session_info(session_name: String, full: Boolean): Session_Info =
      Build_Log.parse_session_info(log_file, session_name, full)

    def parse_header: Header = Build_Log.parse_header(log_file)

    def parse_info: Info = Build_Log.parse_info(log_file)
  }


  /* session log: produced by "isabelle build" */

  sealed case class Session_Info(
    session_name: String,
    session_timing: Properties.T,
    command_timings: List[Properties.T],
    ml_statistics: List[Properties.T],
    task_statistics: List[Properties.T])

  private def parse_session_info(log_file: Log_File, name0: String, full: Boolean): Session_Info =
  {
    val xml_cache = new XML.Cache()

    val session_name =
      log_file.find_line("\fSession.name = ") match {
        case None => name0
        case Some(name) if name0 == "" || name0 == name => name
        case Some(name) => log_file.err("log from different session " + quote(name))
      }
    val session_timing = log_file.find_props("\fTiming = ") getOrElse Nil
    val command_timings = log_file.filter_props("\fcommand_timing = ")
    val ml_statistics = if (full) log_file.filter_props("\fML_statistics = ") else Nil
    val task_statistics = if (full) log_file.filter_props("\ftask_statistics = ") else Nil

    Session_Info(session_name, session_timing, command_timings, ml_statistics, task_statistics)
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

    val Test_Start = new Regex("""^Start test for .+ at (.+), (\w+)$""")
    val Test_End = new Regex("""^End test on (.+), \w+, elapsed time:.*$""")
    val Isabelle_Version = new Regex("""^Isabelle version: .* -- hg id (\w+)$""")
    val AFP_Version = new Regex("""^AFP version: .* -- hg id (\w+)$""")
  }

  private def parse_header(log_file: Log_File): Header =
  {
    log_file.lines match {
      case AFP.Test_Start(start, hostname) :: _ =>
        (start, log_file.lines.last) match {
          case (AFP.Date_Format(start_date), AFP.Test_End(AFP.Date_Format(end_date))) =>
            val isabelle_version =
              log_file.find_match(AFP.Isabelle_Version) getOrElse
                log_file.err("missing Isabelle version")
            val afp_version =
              log_file.find_match(AFP.AFP_Version) getOrElse
                log_file.err("missing AFP version")

            Header(Header_Kind.AFP_TEST,
              List(
                Field.build_host -> hostname,
                Field.build_start -> start_date.toString,
                Field.build_end -> end_date.toString,
                Field.isabelle_version -> isabelle_version,
                Field.afp_version -> afp_version),
              log_file.get_settings(Settings.all_settings))

          case _ => log_file.err("cannot detect start/end date in afp-test log")
        }
      case _ => log_file.err("cannot detect log header format")
    }
  }

  object Session_Status extends Enumeration
  {
    val UNKNOWN = Value("unknown")
    val FINISHED = Value("finished")
    val FAILED = Value("failed")
    val CANCELLED = Value("cancelled")
  }


  /* main log: produced by isatest, afp-test, jenkins etc. */

  sealed case class Info(
    settings: List[(String, String)],
    finished: Map[String, Timing],
    timing: Map[String, Timing],
    threads: Map[String, Int])
  {
    val sessions: Set[String] = finished.keySet ++ timing.keySet

    override def toString: String =
      sessions.toList.sorted.mkString("Build_Log.Info(", ", ", ")")
  }

  private val Session_Finished1 =
    new Regex("""^Finished (\S+) \((\d+):(\d+):(\d+) elapsed time, (\d+):(\d+):(\d+) cpu time.*$""")
  private val Session_Finished2 =
    new Regex("""^Finished (\S+) \((\d+):(\d+):(\d+) elapsed time.*$""")
  private val Session_Timing =
    new Regex("""^Timing (\S+) \((\d) threads, (\d+\.\d+)s elapsed time, (\d+\.\d+)s cpu time, (\d+\.\d+)s GC time.*$""")

  private def parse_info(log_file: Log_File): Info =
  {
    val settings = new mutable.ListBuffer[(String, String)]
    var finished = Map.empty[String, Timing]
    var timing = Map.empty[String, Timing]
    var threads = Map.empty[String, Int]

    for (line <- log_file.lines) {
      line match {
        case Session_Finished1(name,
            Value.Int(e1), Value.Int(e2), Value.Int(e3),
            Value.Int(c1), Value.Int(c2), Value.Int(c3)) =>
          val elapsed = Time.hms(e1, e2, e3)
          val cpu = Time.hms(c1, c2, c3)
          finished += (name -> Timing(elapsed, cpu, Time.zero))
        case Session_Finished2(name,
            Value.Int(e1), Value.Int(e2), Value.Int(e3)) =>
          val elapsed = Time.hms(e1, e2, e3)
          finished += (name -> Timing(elapsed, Time.zero, Time.zero))
        case Session_Timing(name,
            Value.Int(t), Value.Double(e), Value.Double(c), Value.Double(g)) =>
          val elapsed = Time.seconds(e)
          val cpu = Time.seconds(c)
          val gc = Time.seconds(g)
          timing += (name -> Timing(elapsed, cpu, gc))
          threads += (name -> t)
        case Settings.Entry(a, b) if Settings.all_settings.contains(a) =>
          settings += (a -> b)
        case _ =>
      }
    }

    Info(settings.toList, finished, timing, threads)
  }
}
