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

  object Session
  {
    object Key
    {
      object Ordering extends scala.math.Ordering[Key]
      {
        def compare(key1: Key, key2: Key): Int =
          key1.order compare key2.order match {
            case 0 => key1.name compare key2.name
            case ord => ord
          }
      }
    }

    sealed case class Key(name: String, order: Int)
    {
      override def toString: String = name
    }

    sealed case class Info(
      dir: Path,
      description: String,
      options: Options,
      theories: List[(Options, String)],
      files: List[String])

    object Queue
    {
      val empty: Queue = new Queue()
    }

    final class Queue private(
      keys: Map[String, Key] = Map.empty,
      graph: Graph[Key, Info] = Graph.empty(Key.Ordering))
    {
      def defined(name: String): Boolean = keys.isDefinedAt(name)

      def + (key: Key, info: Info, parent: Option[String]): Queue =
      {
        val keys1 =
          if (defined(key.name)) error("Duplicate session: " + quote(key.name))
          else keys + (key.name -> key)

        val graph1 =
          try {
            graph.new_node(key, info).add_deps_acyclic(key, parent.toList.map(keys(_)))
          }
          catch {
            case exn: Graph.Cycles[_] =>
              error(cat_lines(exn.cycles.map(cycle =>
                "Cyclic session dependency of " +
                  cycle.map(key => quote(key.toString)).mkString(" via "))))
          }
        new Queue(keys1, graph1)
      }

      def topological_order: List[(Key, Info)] =
        graph.topological_order.map(key => (key, graph.get_node(key)))
    }
  }


  /* parsing */

  private case class Session_Entry(
    name: String,
    reset: Boolean,
    order: Int,
    path: Option[String],
    parent: Option[String],
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
        (keyword("(") ~! (nat <~ keyword(")")) ^^ { case _ ~ x => x } | success(Integer.MAX_VALUE)) ~
        (opt(keyword(IN) ~! string ^^ { case _ ~ x => x })) ~
        (keyword("=") ~> opt(session_name <~ keyword("+"))) ~
        (keyword(DESCRIPTION) ~! text ^^ { case _ ~ x => x } | success("")) ~
        (keyword(OPTIONS) ~! options ^^ { case _ ~ x => x } | success(Nil)) ~
        rep(theories) ~
        (keyword(FILES) ~! rep1(path) ^^ { case _ ~ x => x } | success(Nil)) ^^
          { case a ~ b ~ c ~ d ~ e ~ f ~ g ~ h ~ i => Session_Entry(a, b, c, d, e, f, g, h, i) }
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

  private def sessions_root(dir: Path, root: File, sessions: Session.Queue): Session.Queue =
  {
    (sessions /: Parser.parse_entries(root))((sessions1, entry) =>
      try {
        if (entry.name == "") error("Bad session name")

        val full_name =
          if (entry.name == "RAW" || entry.name == "Pure") {
            if (entry.parent.isDefined) error("Illegal parent session")
            else entry.name
          }
          else
            entry.parent match {
              case Some(parent_name) if sessions1.defined(parent_name) =>
                if (entry.reset) entry.name
                else parent_name + "-" + entry.name
              case _ => error("Bad parent session")
            }

        val path =
          entry.path match {
            case Some(p) => Path.explode(p)
            case None => Path.basic(entry.name)
          }

        val key = Session.Key(full_name, entry.order)
        val info = Session.Info(dir + path, entry.description, entry.options,
          entry.theories.map({ case (x, ys) => ys.map(y => (x, y)) }).flatten, entry.files)

        sessions1 + (key, info, entry.parent)
      }
      catch {
        case ERROR(msg) =>
          error(msg + "\nThe error(s) above occurred in session entry " +
            quote(entry.name) + " (file " + quote(root.toString) + ")")
      })
  }

  private def sessions_dir(strict: Boolean, dir: Path, sessions: Session.Queue): Session.Queue =
  {
    val root = Isabelle_System.platform_file(dir + Path.basic("ROOT"))
    if (root.isFile) sessions_root(dir, root, sessions)
    else if (strict) error("Bad session root file: " + quote(root.toString))
    else sessions
  }

  private def sessions_catalog(dir: Path, catalog: File, sessions: Session.Queue): Session.Queue =
  {
    val dirs =
      split_lines(Standard_System.read_file(catalog)).
        filterNot(line => line == "" || line.startsWith("#"))
    (sessions /: dirs)((sessions1, dir1) =>
      try {
        val dir2 = dir + Path.explode(dir1)
        if (Isabelle_System.platform_file(dir2).isDirectory) sessions_dir(true, dir2, sessions1)
        else error("Bad session directory: " + dir2.toString)
      }
      catch {
        case ERROR(msg) =>
          error(msg + "\nThe error(s) above occurred in session catalog " + quote(catalog.toString))
      })
  }

  def find_sessions(more_dirs: List[Path]): Session.Queue =
  {
    var sessions = Session.Queue.empty

    for (dir <- Isabelle_System.components()) {
      sessions = sessions_dir(false, dir, sessions)

      val catalog = Isabelle_System.platform_file(dir + Path.explode("etc/sessions"))
      if (catalog.isFile)
        sessions = sessions_catalog(dir, catalog, sessions)
    }

    for (dir <- more_dirs) sessions = sessions_dir(true, dir, sessions)

    sessions
  }



  /** build **/

  def build(all_sessions: Boolean, build_images: Boolean, list_only: Boolean,
    more_dirs: List[Path], options: List[String], sessions: List[String]): Int =
  {
    println("more_dirs = " + more_dirs.toString)
    println("options = " + options.toString)
    println("sessions = " + sessions.toString)

    for ((key, info) <- find_sessions(more_dirs).topological_order)
      println(key.name + " in " + info.dir)

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

