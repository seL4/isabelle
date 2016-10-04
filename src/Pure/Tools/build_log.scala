/*  Title:      Pure/Tools/build_log.scala
    Author:     Makarius

Build log parsing for historic versions, back to "build_history_base".
*/

package isabelle


object Build_Log
{
  /* inlined properties (YXML) */

  object Props
  {
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
}
