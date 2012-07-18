/*  Title:      Pure/System/build.scala
    Author:     Makarius

Build and manage Isabelle sessions.
*/

package isabelle


import java.io.File


object Build
{
  /* command line entry point */

  private object Bool
  {
    def unapply(s: String): Option[Boolean] =
      s match {
        case "true" => Some(true)
        case "false" => Some(false)
        case _ => None
      }
  }

  def main(args: Array[String])
  {
    def bad_args(): Nothing = error("Bad arguments: " + args.toString)

    val rc =
      try {
        args.toList match {
          case Bool(all_sessions) :: Bool(build_images) :: Bool(list_only) :: rest =>
            rest.indexWhere(_ == "\n") match {
              case -1 => bad_args()
              case i =>
                val (options, rest1) = rest.splitAt(i)
                val sessions = rest1.tail
                build(all_sessions, build_images, list_only, options, sessions)
            }
          case _ => bad_args()
        }
      }
      catch {
        case exn: Throwable => java.lang.System.err.println(Exn.message(exn)); 2
      }

    sys.exit(rc)
  }


  /* build */

  def build(all_sessions: Boolean, build_images: Boolean, list_only: Boolean,
    options: List[String], sessions: List[String]): Int =
  {
    println("options = " + options.toString)
    println("sessions = " + sessions.toString)

    find_sessions() foreach println

    0
  }


  /* session information */

  val ROOT_NAME = "ROOT"

  type Options = List[(String, Option[String])]

  case class Session_Info(
    dir: Path,
    name: String,
    reset_name: Boolean,
    parent: String,
    description: String,
    options: Options,
    theories: List[(Options, String)],
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

    def session_info(dir: Path): Parser[Session_Info] =
    {
      val session_name = atom("session name", _.is_name)
      val theory_name = atom("theory name", _.is_name)

      val option =
        name ~ opt(keyword("=") ~! name ^^ { case _ ~ x => x }) ^^ { case x ~ y => (x, y) }
      val options: Parser[Options] =
        keyword("[") ~> repsep(option, keyword(",")) <~ keyword("]")

      val theories =
        keyword(THEORIES) ~! ((options | success(Nil)) ~ rep1(theory_name)) ^^
          { case _ ~ (x ~ y) => (x, y) }

      ((keyword(SESSION) ~! session_name) ^^ { case _ ~ x => x }) ~
        (keyword("!") ^^^ true | success(false)) ~
        (opt(keyword(IN) ~! string ^^ { case _ ~ x => Path.explode(x) })) ~
        (keyword("=") ~> session_name <~ keyword("+")) ~
        (keyword(DESCRIPTION) ~! text ^^ { case _ ~ x => x } | success("")) ~
        (keyword(OPTIONS) ~! options ^^ { case _ ~ x => x } | success(Nil)) ~
        rep(theories) ~
        (keyword(FILES) ~! rep1(path) ^^ { case _ ~ x => x } | success(Nil)) ^^
          { case a ~ b ~ c ~ d ~ e ~ f ~ g ~ h =>
              val dir1 = dir + c.getOrElse(Path.basic(a))
              val thys = g.map({ case (x, ys) => ys.map(y => (x, y)) }).flatten
              Session_Info(dir1, a, b, d, e, f, thys, h) }
    }

    def parse_entries(dir: Path, root: File): List[Session_Info] =
    {
      val toks = syntax.scan(Standard_System.read_file(root))
      parse_all(rep(session_info(dir)), Token.reader(toks, root.toString)) match {
        case Success(result, _) => result
        case bad => error(bad.toString)
      }
    }
  }

  def find_sessions(): List[Session_Info] =
  {
    for {
      dir <- Isabelle_System.components()
      root = Isabelle_System.platform_file(dir + Path.basic(ROOT_NAME))
      if root.isFile
      entry <- Parser.parse_entries(dir, root)
    } yield entry
  }
}

