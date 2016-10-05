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
  /* inlined properties (YXML) */

  object Props
  {
    def print(props: Properties.T): String = YXML.string_of_body(XML.Encode.properties(props))
    def parse(text: String): Properties.T = XML.Decode.properties(YXML.parse_body(text))

    def parse_lines(prefix: String, lines: List[String]): List[Properties.T] =
      for (line <- lines; s <- Library.try_unprefix(prefix, line)) yield parse(s)

    def find_parse_line(prefix: String, lines: List[String]): Option[Properties.T] =
      lines.find(_.startsWith(prefix)).map(line => parse(line.substring(prefix.length)))
  }


  /* session log: produced by "isabelle build" */

  sealed case class Session_Info(
    session_name: String,
    session_timing: Properties.T,
    command_timings: List[Properties.T],
    ml_statistics: List[Properties.T],
    task_statistics: List[Properties.T])

  val SESSION_NAME = "\fSession.name = "

  def parse_session_info(name0: String, lines: List[String], full: Boolean): Session_Info =
  {
    val xml_cache = new XML.Cache()
    def parse_lines(prfx: String): List[Properties.T] =
      Props.parse_lines(prfx, lines).map(xml_cache.props(_))

    val session_name =
      lines.find(_.startsWith(SESSION_NAME)).map(_.substring(SESSION_NAME.length)) match {
        case None => name0
        case Some(name) if name0 == "" || name0 == name => name
        case Some(name) =>
          error("Session log for " + quote(name0) + " is actually from " + quote(name))
      }
    val session_timing = Props.find_parse_line("\fTiming = ", lines) getOrElse Nil
    val command_timings = parse_lines("\fcommand_timing = ")
    val ml_statistics = if (full) parse_lines("\fML_statistics = ") else Nil
    val task_statistics = if (full) parse_lines("\ftask_statistics = ") else Nil

    Session_Info(session_name, session_timing, command_timings, ml_statistics, task_statistics)
  }


  /* header and data fields */

  object Header_Kind extends Enumeration
  {
    val ISATEST = Value("isatest")
    val AFP_TEST = Value("afp-test")
    val JENKINS = Value("jenkins")
  }

  sealed case class Header(kind: Header_Kind.Value, props: Properties.T, settings: List[String])

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
    val settings =
      List("ISABELLE_BUILD_OPTIONS=", "ML_PLATFORM=", "ML_HOME=", "ML_SYSTEM=", "ML_OPTIONS=")
  }

  def parse_header(lines: List[String]): Header =
  {
    val proper_lines = lines.filterNot(line => line.forall(Character.isWhitespace(_)))

    def err(msg: String): Nothing = error(cat_lines((msg + ":") :: lines.take(10)))

    proper_lines match {
      case AFP.Test_Start(start, hostname) :: _ =>
        (start, proper_lines.last) match {
          case (AFP.Date_Format(start_date), AFP.Test_End(AFP.Date_Format(end_date))) =>
            val props =
              List(
                Field.build_host -> hostname,
                Field.build_start -> start_date.toString,
                Field.build_end -> end_date.toString) :::
              lines.collectFirst(
                { case AFP.Isabelle_Version(id) => Field.isabelle_version -> id }).toList :::
              lines.collectFirst(
                { case AFP.AFP_Version(id) => Field.afp_version -> id }).toList
            val settings = lines.filter(line => AFP.settings.exists(line.startsWith(_)))
            Header(Header_Kind.AFP_TEST, props, settings)
          case _ => err("Malformed start/end date in afp-test log")
        }
      case _ => err("Failed to detect build log header")
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
    ml_options: List[(String, String)],
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

  private object ML_Option
  {
    def unapply(s: String): Option[(String, String)] =
      s.indexOf('=') match {
        case -1 => None
        case i =>
          val a = s.substring(0, i)
          Library.try_unquote(s.substring(i + 1)) match {
            case Some(b) if Build.ml_options.contains(a) => Some((a, b))
            case _ => None
          }
      }
  }

  def parse_info(text: String): Info =
  {
    val ml_options = new mutable.ListBuffer[(String, String)]
    var finished = Map.empty[String, Timing]
    var timing = Map.empty[String, Timing]
    var threads = Map.empty[String, Int]

    for (line <- split_lines(text)) {
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
        case ML_Option(a, b) => ml_options += (a -> b)
        case _ =>
      }
    }

    Info(ml_options.toList, finished, timing, threads)
  }
}
