/*  Title:      Pure/System/build.scala
    Author:     Makarius

Build and manage Isabelle sessions.
*/

package isabelle


import java.io.File

import scala.collection.mutable
import scala.annotation.tailrec


object Build
{
  /** session information **/

  type Options = List[(String, Option[String])]

  case class Session_Info(
    dir: Path,
    name: String,
    parent: String,
    description: String,
    options: Options,
    theories: List[(Options, String)],
    files: List[String])

  private val pure_info =
    Session_Info(Path.current, "Pure", "", "", Nil, List((Nil, "Pure")), Nil)


  /* parsing */

  val ROOT_NAME = "ROOT"

  private case class Session_Entry(
    name: String,
    reset: Boolean,
    path: Option[String],
    parent: String,
    description: String,
    options: Options,
    theories: List[(Options, List[String])],
    files: List[String])

  private object Parser extends Parse.Parser
  {
    val SESSION = "session"
    val IN = "in"
    val DESCRIPTION = "description"
    val OPTIONS = "options"
    val THEORIES = "theories"
    val FILES = "files"

    val syntax =
      Outer_Syntax.empty + "!" + "(" + ")" + "+" + "," + "=" + "[" + "]" +
        SESSION + IN + DESCRIPTION + OPTIONS + THEORIES + FILES

    val session_entry: Parser[Session_Entry] =
    {
      val session_name = atom("session name", _.is_name)
      val theory_name = atom("theory name", _.is_name)

      val option =
        name ~ opt(keyword("=") ~! name ^^ { case _ ~ x => x }) ^^ { case x ~ y => (x, y) }
      val options = keyword("[") ~> repsep(option, keyword(",")) <~ keyword("]")

      val theories =
        keyword(THEORIES) ~! ((options | success(Nil)) ~ rep1(theory_name)) ^^
          { case _ ~ (x ~ y) => (x, y) }

      ((keyword(SESSION) ~! session_name) ^^ { case _ ~ x => x }) ~
        (keyword("!") ^^^ true | success(false)) ~
        (opt(keyword(IN) ~! string ^^ { case _ ~ x => x })) ~
        (keyword("=") ~> session_name <~ keyword("+")) ~
        (keyword(DESCRIPTION) ~! text ^^ { case _ ~ x => x } | success("")) ~
        (keyword(OPTIONS) ~! options ^^ { case _ ~ x => x } | success(Nil)) ~
        rep1(theories) ~
        (keyword(FILES) ~! rep1(path) ^^ { case _ ~ x => x } | success(Nil)) ^^
          { case a ~ b ~ c ~ d ~ e ~ f ~ g ~ h => Session_Entry(a, b, c, d, e, f, g, h) }
    }

    def parse_entries(root: File): List[Session_Entry] =
    {
      val toks = syntax.scan(Standard_System.read_file(root))
      parse_all(rep(session_entry), Token.reader(toks, root.toString)) match {
        case Success(result, _) => result
        case bad => error(bad.toString)
      }
    }
  }


  /* find sessions */

  def find_sessions(more_dirs: List[Path]): List[Session_Info] =
  {
    val infos = new mutable.ListBuffer[Session_Info]
    infos += pure_info

    for {
      (dir, strict) <- Isabelle_System.components().map((_, false)) ++ more_dirs.map((_, true))
      root = Isabelle_System.platform_file(dir + Path.basic(ROOT_NAME))
      _ = (strict && !root.isFile && error("Bad session root file: " + quote(root.toString)))
      if root.isFile
      entry <- Parser.parse_entries(root)
    }
    {
      try {
        val parent =
          infos.find(_.name == entry.parent) getOrElse
           error("Unknown parent session: " + quote(entry.parent))
        val full_name =
          if (entry.reset) entry.name
          else parent.name + "-" + entry.name

        if (entry.name == "") error("Bad session name")
        if (infos.exists(_.name == full_name))
          error("Duplicate session name: " + quote(full_name))

        val path =
          entry.path match {
            case Some(p) => Path.explode(p)
            case None => Path.basic(entry.name)
          }
        val thys = entry.theories.map({ case (x, ys) => ys.map(y => (x, y)) }).flatten
        val info =
          Session_Info(dir + path, full_name, entry.parent, entry.description,
            entry.options, thys, entry.files)

        infos += info
      }
      catch {
        case ERROR(msg) =>
          error(msg + "\nThe error(s) above occurred in session entry " +
            quote(entry.name) + " (file " + quote(root.toString) + ")")
      }
    }
    infos.toList
  }



  /** build **/

  def build(all_sessions: Boolean, build_images: Boolean, list_only: Boolean,
    more_dirs: List[Path], options: List[String], sessions: List[String]): Int =
  {
    println("more_dirs = " + more_dirs.toString)
    println("options = " + options.toString)
    println("sessions = " + sessions.toString)

    find_sessions(more_dirs) foreach println

    0
  }


  /* command line entry point */

  def main(args: Array[String])
  {
    Command_Line.tool {
      args.toList match {
        case
          Properties.Value.Boolean(all_sessions) ::
          Properties.Value.Boolean(build_images) ::
          Properties.Value.Boolean(list_only) ::
          Command_Line.Chunks(more_dirs, options, sessions) =>
            build(all_sessions, build_images, list_only,
              more_dirs.map(Path.explode), options, sessions)
        case _ => error("Bad arguments:\n" + cat_lines(args))
      }
    }
  }
}

