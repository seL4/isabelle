/*  Title:      Pure/System/build.scala
    Author:     Makarius

Build and manage Isabelle sessions.
*/

package isabelle


import java.io.{File => JFile}

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

      def required(names: List[String]): Queue =
      {
        val req = graph.all_preds(names.map(keys(_))).map(_.name).toSet
        val keys1 = keys -- keys.keySet.filter(name => !req(name))
        val graph1 = graph.restrict(key => keys1.isDefinedAt(key.name))
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

    def parse_entries(root: JFile): List[Session_Entry] =
    {
      val toks = syntax.scan(File.read(root))
      parse_all(rep(session_entry), Token.reader(toks, root.toString)) match {
        case Success(result, _) => result
        case bad => error(bad.toString)
      }
    }
  }


  /* find sessions */

  private val ROOT = Path.explode("ROOT")
  private val SESSIONS = Path.explode("etc/sessions")

  private def is_pure(name: String): Boolean = name == "RAW" || name == "Pure"

  private def sessions_root(dir: Path, root: JFile, queue: Session.Queue): Session.Queue =
  {
    (queue /: Parser.parse_entries(root))((queue1, entry) =>
      try {
        if (entry.name == "") error("Bad session name")

        val full_name =
          if (is_pure(entry.name)) {
            if (entry.parent.isDefined) error("Illegal parent session")
            else entry.name
          }
          else
            entry.parent match {
              case Some(parent_name) if queue1.defined(parent_name) =>
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

        queue1 + (key, info, entry.parent)
      }
      catch {
        case ERROR(msg) =>
          error(msg + "\nThe error(s) above occurred in session entry " +
            quote(entry.name) + Position.str_of(Position.file(root)))
      })
  }

  private def sessions_dir(strict: Boolean, dir: Path, queue: Session.Queue): Session.Queue =
  {
    val root = (dir + ROOT).file
    if (root.isFile) sessions_root(dir, root, queue)
    else if (strict) error("Bad session root file: " + quote(root.toString))
    else queue
  }

  private def sessions_catalog(dir: Path, catalog: JFile, queue: Session.Queue): Session.Queue =
  {
    val dirs =
      split_lines(File.read(catalog)).filterNot(line => line == "" || line.startsWith("#"))
    (queue /: dirs)((queue1, dir1) =>
      try {
        val dir2 = dir + Path.explode(dir1)
        if (dir2.file.isDirectory) sessions_dir(true, dir2, queue1)
        else error("Bad session directory: " + dir2.toString)
      }
      catch {
        case ERROR(msg) =>
          error(msg + "\nThe error(s) above occurred in session catalog " + quote(catalog.toString))
      })
  }

  def find_sessions(more_dirs: List[Path]): Session.Queue =
  {
    var queue = Session.Queue.empty

    for (dir <- Isabelle_System.components()) {
      queue = sessions_dir(false, dir, queue)

      val catalog = (dir + SESSIONS).file
      if (catalog.isFile)
        queue = sessions_catalog(dir, catalog, queue)
    }

    for (dir <- more_dirs) queue = sessions_dir(true, dir, queue)

    queue
  }



  /** build **/

  private def echo(msg: String) { java.lang.System.out.println(msg) }
  private def echo_n(msg: String) { java.lang.System.out.print(msg) }

  private def build_job(build_images: Boolean,  // FIXME
    key: Session.Key, info: Session.Info): Isabelle_System.Bash_Job =
  {
    val cwd = info.dir.file
    val script =
      if (is_pure(key.name)) "./build " + (if (build_images) "-b " else "") + key.name
      else """echo "Bad session" >&2; exit 2"""
    new Isabelle_System.Bash_Job(cwd, null, script)
  }

  def build(all_sessions: Boolean, build_images: Boolean, list_only: Boolean,
    more_dirs: List[Path], options: List[String], sessions: List[String]): Int =
  {
    val full_queue = find_sessions(more_dirs)
    val build_options = (Options.init() /: options)(_.define_simple(_))

    sessions.filter(name => !full_queue.defined(name)) match {
      case Nil =>
      case bad => error("Undefined session(s): " + commas_quote(bad))
    }

    val required_queue =
      if (all_sessions) full_queue
      else full_queue.required(sessions)

    // prepare browser info dir
    if (build_options.bool("browser_info") &&
      !Path.explode("$ISABELLE_BROWSER_INFO/index.html").file.isFile)
    {
      Path.explode("$ISABELLE_BROWSER_INFO").file.mkdirs()
      File.copy(Path.explode("$ISABELLE_HOME/lib/logo/isabelle.gif"),
        Path.explode("$ISABELLE_BROWSER_INFO/isabelle.gif"))
      File.write(Path.explode("$ISABELLE_BROWSER_INFO/index.html"),
        File.read(Path.explode("$ISABELLE_HOME/lib/html/library_index_header.template")) +
        File.read(Path.explode("$ISABELLE_HOME/lib/html/library_index_content.template")) +
        File.read(Path.explode("$ISABELLE_HOME/lib/html/library_index_footer.template")))
    }

    // prepare log dir
    val log_dir = Path.explode("$ISABELLE_OUTPUT/log")
    log_dir.file.mkdirs()

    // run jobs
    val rcs =
      for ((key, info) <- required_queue.topological_order) yield
      {
        if (list_only) { echo(key.name + " in " + info.dir); 0 }
        else {
          if (build_images) echo("Building " + key.name + "...")
          else echo("Running " + key.name + "...")

          val (out, err, rc) = build_job(build_images, key, info).join
          echo_n(err)

          val log = log_dir + Path.basic(key.name)
          if (rc == 0) {
            File.write_zip(log.ext("gz"), out)
          }
          else {
            File.write(log, out)
            echo(key.name + " FAILED")
            echo("(see also " + log.file + ")")
            val lines = split_lines(out)
            val tail = lines.drop(lines.length - 20 max 0)
            echo("\n" + cat_lines(tail))
          }
          rc
        }
      }
    (0 /: rcs)(_ max _)
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

