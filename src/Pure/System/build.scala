/*  Title:      Pure/System/build.scala
    Author:     Makarius

Build and manage Isabelle sessions.
*/

package isabelle


import java.util.{Timer, TimerTask}
import java.io.{BufferedInputStream, FileInputStream,
  BufferedReader, InputStreamReader, IOException}
import java.util.zip.GZIPInputStream

import scala.collection.SortedSet
import scala.annotation.tailrec


object Build
{
  /** session information **/

  // external version
  sealed case class Session_Entry(
    pos: Position.T,
    base_name: String,
    this_name: Boolean,
    groups: List[String],
    path: Option[String],
    parent: Option[String],
    description: String,
    options: List[Options.Spec],
    theories: List[(List[Options.Spec], List[String])],
    files: List[String])

  // internal version
  sealed case class Session_Info(
    pos: Position.T,
    groups: List[String],
    dir: Path,
    parent: Option[String],
    description: String,
    options: Options,
    theories: List[(Options, List[Path])],
    files: List[Path],
    entry_digest: SHA1.Digest)

  def is_pure(name: String): Boolean = name == "RAW" || name == "Pure"

  def session_info(options: Options, dir: Path, entry: Session_Entry): (String, Session_Info) =
    try {
      if (entry.base_name == "") error("Bad session name")

      val full_name =
        if (is_pure(entry.base_name)) {
          if (entry.parent.isDefined) error("Illegal parent session")
          else entry.base_name
        }
        else
          entry.parent match {
            case None => error("Missing parent session")
            case Some(parent_name) =>
              if (entry.this_name) entry.base_name
              else parent_name + "-" + entry.base_name
          }

      val path =
        entry.path match {
          case Some(p) => Path.explode(p)
          case None => Path.basic(entry.base_name)
        }

      val session_options = options ++ entry.options

      val theories =
        entry.theories.map({ case (opts, thys) =>
          (session_options ++ opts, thys.map(Path.explode(_))) })
      val files = entry.files.map(Path.explode(_))
      val entry_digest =
        SHA1.digest((full_name, entry.parent, entry.options, entry.theories).toString)

      val info =
        Session_Info(entry.pos, entry.groups, dir + path, entry.parent, entry.description,
          session_options, theories, files, entry_digest)

      (full_name, info)
    }
    catch {
      case ERROR(msg) =>
        error(msg + "\nThe error(s) above occurred in session entry " +
          quote(entry.base_name) + Position.str_of(entry.pos))
    }


  /* session tree */

  object Session_Tree
  {
    def apply(infos: Seq[(String, Session_Info)]): Session_Tree =
    {
      val graph1 =
        (Graph.string[Session_Info] /: infos) {
          case (graph, (name, info)) =>
            if (graph.defined(name))
              error("Duplicate session " + quote(name) + Position.str_of(info.pos))
            else graph.new_node(name, info)
        }
      val graph2 =
        (graph1 /: graph1.entries) {
          case (graph, (name, (info, _))) =>
            info.parent match {
              case None => graph
              case Some(parent) =>
                if (!graph.defined(parent))
                  error("Bad parent session " + quote(parent) + " for " +
                    quote(name) + Position.str_of(info.pos))

                try { graph.add_edge_acyclic(parent, name) }
                catch {
                  case exn: Graph.Cycles[_] =>
                    error(cat_lines(exn.cycles.map(cycle =>
                      "Cyclic session dependency of " +
                        cycle.map(c => quote(c.toString)).mkString(" via "))) +
                          Position.str_of(info.pos))
                }
            }
        }
      new Session_Tree(graph2)
    }
  }

  final class Session_Tree private(val graph: Graph[String, Session_Info])
    extends PartialFunction[String, Session_Info]
  {
    def apply(name: String): Session_Info = graph.get_node(name)
    def isDefinedAt(name: String): Boolean = graph.defined(name)

    def required(all_sessions: Boolean, session_groups: List[String], sessions: List[String])
      : (List[String], Session_Tree) =
    {
      val bad_sessions = sessions.filterNot(isDefinedAt(_))
      if (!bad_sessions.isEmpty) error("Undefined session(s): " + commas_quote(bad_sessions))

      val selected =
      {
        if (all_sessions) graph.keys.toList
        else {
          val sel_group = session_groups.toSet
          val sel = sessions.toSet
            graph.keys.toList.filter(name =>
              sel(name) || apply(name).groups.exists(sel_group)).toList
        }
      }
      val descendants = graph.all_succs(selected)
      val tree1 = new Session_Tree(graph.restrict(graph.all_preds(selected).toSet))
      (descendants, tree1)
    }

    def topological_order: List[(String, Session_Info)] =
      graph.topological_order.map(name => (name, apply(name)))
  }


  /* parser */

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

    def session_entry(pos: Position.T): Parser[Session_Entry] =
    {
      val session_name = atom("session name", _.is_name)

      val option =
        name ~ opt(keyword("=") ~! name ^^ { case _ ~ x => x }) ^^ { case x ~ y => (x, y) }
      val options = keyword("[") ~> repsep(option, keyword(",")) <~ keyword("]")

      val theories =
        keyword(THEORIES) ~! ((options | success(Nil)) ~ rep1(theory_name)) ^^
          { case _ ~ (x ~ y) => (x, y) }

      ((keyword(SESSION) ~! session_name) ^^ { case _ ~ x => x }) ~
        (keyword("!") ^^^ true | success(false)) ~
        (keyword("(") ~! (rep1(name) <~ keyword(")")) ^^ { case _ ~ x => x } | success(Nil)) ~
        (opt(keyword(IN) ~! path ^^ { case _ ~ x => x })) ~
        (keyword("=") ~> opt(session_name <~ keyword("+"))) ~
        (keyword(DESCRIPTION) ~! text ^^ { case _ ~ x => x } | success("")) ~
        (keyword(OPTIONS) ~! options ^^ { case _ ~ x => x } | success(Nil)) ~
        rep(theories) ~
        (keyword(FILES) ~! rep1(path) ^^ { case _ ~ x => x } | success(Nil)) ^^
          { case a ~ b ~ c ~ d ~ e ~ f ~ g ~ h ~ i => Session_Entry(pos, a, b, c, d, e, f, g, h, i) }
    }

    def parse_entries(root: Path): List[Session_Entry] =
    {
      val toks = syntax.scan(File.read(root))
      parse_all(rep(session_entry(root.position)), Token.reader(toks, root.implode)) match {
        case Success(result, _) => result
        case bad => error(bad.toString)
      }
    }
  }


  /* find sessions within certain directories */

  private val ROOT = Path.explode("ROOT")
  private val ROOTS = Path.explode("ROOTS")

  private def is_session_dir(dir: Path): Boolean =
    (dir + ROOT).is_file || (dir + ROOTS).is_file

  private def check_session_dir(dir: Path): Path =
    if (is_session_dir(dir)) dir
    else error("Bad session root directory: " + dir.toString)

  def find_sessions(options: Options, more_dirs: List[Path]): Session_Tree =
  {
    def find_dir(dir: Path): List[(String, Session_Info)] = find_root(dir) ::: find_roots(dir)

    def find_root(dir: Path): List[(String, Session_Info)] =
    {
      val root = dir + ROOT
      if (root.is_file) Parser.parse_entries(root).map(session_info(options, dir, _))
      else Nil
    }

    def find_roots(dir: Path): List[(String, Session_Info)] =
    {
      val roots = dir + ROOTS
      if (roots.is_file) {
        for {
          line <- split_lines(File.read(roots))
          if !(line == "" || line.startsWith("#"))
          dir1 =
            try { check_session_dir(dir + Path.explode(line)) }
            catch {
              case ERROR(msg) =>
                error(msg + "\nThe error(s) above occurred in session catalog " + roots.toString)
            }
          info <- find_dir(dir1)
        } yield info
      }
      else Nil
    }

    Session_Tree(
      for {
        dir <-
          Isabelle_System.components().filter(is_session_dir(_)) :::
          more_dirs.map(check_session_dir(_))
        info <- find_dir(dir)
      } yield info)
  }



  /** build **/

  private def echo(msg: String) { java.lang.System.out.println(msg) }
  private def sleep(): Unit = Thread.sleep(500)


  /* queue */

  object Queue
  {
    def apply(tree: Session_Tree): Queue =
    {
      val graph = tree.graph

      def outdegree(name: String): Int = graph.imm_succs(name).size
      def timeout(name: String): Double = tree(name).options.real("timeout")

      object Ordering extends scala.math.Ordering[String]
      {
        def compare(name1: String, name2: String): Int =
          outdegree(name2) compare outdegree(name1) match {
            case 0 =>
              timeout(name2) compare timeout(name1) match {
                case 0 => name1 compare name2
                case ord => ord
              }
            case ord => ord
          }
      }

      new Queue(graph, SortedSet(graph.keys.toList: _*)(Ordering))
    }
  }

  final class Queue private(graph: Graph[String, Session_Info], order: SortedSet[String])
  {
    def is_inner(name: String): Boolean = !graph.is_maximal(name)

    def is_empty: Boolean = graph.is_empty

    def - (name: String): Queue = new Queue(graph.del_node(name), order - name)

    def dequeue(skip: String => Boolean): Option[(String, Session_Info)] =
    {
      val it = order.iterator.dropWhile(name => skip(name) || !graph.is_minimal(name))
      if (it.hasNext) { val name = it.next; Some((name, graph.get_node(name))) }
      else None
    }
  }


  /* source dependencies */

  sealed case class Node(
    loaded_theories: Set[String],
    syntax: Outer_Syntax,
    sources: List[(Path, SHA1.Digest)])

  sealed case class Deps(deps: Map[String, Node])
  {
    def is_empty: Boolean = deps.isEmpty
    def apply(name: String): Node = deps(name)
    def sources(name: String): List[SHA1.Digest] = deps(name).sources.map(_._2)
  }

  def dependencies(verbose: Boolean, tree: Session_Tree): Deps =
    Deps((Map.empty[String, Node] /: tree.topological_order)(
      { case (deps, (name, info)) =>
          val (preloaded, parent_syntax) =
            info.parent match {
              case Some(parent) => (deps(parent).loaded_theories, deps(parent).syntax)
              case None =>
                (Set.empty[String],
                  Outer_Syntax.init() +
                    // FIXME avoid hardwired stuff!?
                    ("theory", Keyword.THY_BEGIN) +
                    ("hence", Keyword.PRF_ASM_GOAL, "then have") +
                    ("thus", Keyword.PRF_ASM_GOAL, "then show"))
            }
          val thy_info = new Thy_Info(new Thy_Load(preloaded))

          if (verbose) {
            val groups =
              if (info.groups.isEmpty) ""
              else info.groups.mkString(" (", " ", ")")
            echo("Session " + name + groups)
          }

          val thy_deps =
            thy_info.dependencies(
              info.theories.map(_._2).flatten.
                map(thy => Document.Node.Name(info.dir + Thy_Load.thy_path(thy))))

          val loaded_theories = preloaded ++ thy_deps.map(_._1.theory)

          val keywords = thy_deps.map({ case (_, Exn.Res(h)) => h.keywords case _ => Nil }).flatten
          val syntax = (parent_syntax /: keywords)(_ + _)

          val all_files =
            thy_deps.map({ case (n, h) =>
              val thy = Path.explode(n.node).expand
              val uses =
                h match {
                  case Exn.Res(d) =>
                    d.uses.map(p => (Path.explode(n.dir) + Path.explode(p._1)).expand)
                  case _ => Nil
                }
              thy :: uses
            }).flatten ::: info.files.map(file => info.dir + file)
          val sources =
            try { all_files.map(p => (p, SHA1.digest(p))) }
            catch {
              case ERROR(msg) =>
                error(msg + "\nThe error(s) above occurred in session " +
                  quote(name) + Position.str_of(info.pos))
            }

          deps + (name -> Node(loaded_theories, syntax, sources))
      }))


  /* jobs */

  private class Job(name: String, info: Session_Info, output: Path, do_output: Boolean,
    verbose: Boolean, browser_info: Path)
  {
    // global browser info dir
    if (info.options.bool("browser_info") && !(browser_info + Path.explode("index.html")).is_file)
    {
      browser_info.file.mkdirs()
      File.copy(Path.explode("~~/lib/logo/isabelle.gif"),
        browser_info + Path.explode("isabelle.gif"))
      File.write(browser_info + Path.explode("index.html"),
        File.read(Path.explode("~~/lib/html/library_index_header.template")) +
        File.read(Path.explode("~~/lib/html/library_index_content.template")) +
        File.read(Path.explode("~~/lib/html/library_index_footer.template")))
    }

    def output_path: Option[Path] = if (do_output) Some(output) else None

    private val parent = info.parent.getOrElse("")

    private val args_file = File.tmp_file("args")
    File.write(args_file, YXML.string_of_body(
      if (is_pure(name)) Options.encode(info.options)
      else
        {
          import XML.Encode._
              pair(bool, pair(Options.encode, pair(bool, pair(Path.encode, pair(string,
                pair(string, list(pair(Options.encode, list(Path.encode)))))))))(
              (do_output, (info.options, (verbose, (browser_info, (parent,
                (name, info.theories)))))))
        }))

    private val env =
      Map("INPUT" -> parent, "TARGET" -> name, "OUTPUT" -> Isabelle_System.standard_path(output),
        (if (is_pure(name)) "ISABELLE_PROCESS_OPTIONS" else "ARGS_FILE") ->
          Isabelle_System.posix_path(args_file.getPath))

    private val script =
      if (is_pure(name)) {
        if (do_output) "./build " + name + " \"$OUTPUT\""
        else """ rm -f "$OUTPUT"; ./build """ + name
      }
      else {
        """
        . "$ISABELLE_HOME/lib/scripts/timestart.bash"
        """ +
          (if (do_output)
            """
            "$ISABELLE_PROCESS" -e "Build.build \"$ARGS_FILE\";" -q -w "$INPUT" "$OUTPUT"
            """
          else
            """
            rm -f "$OUTPUT"; "$ISABELLE_PROCESS" -e "Build.build \"$ARGS_FILE\";" -r -q "$INPUT"
            """) +
        """
        RC="$?"

        . "$ISABELLE_HOME/lib/scripts/timestop.bash"

        if [ "$RC" -eq 0 ]; then
          echo "Finished $TARGET ($TIMES_REPORT)" >&2
        fi

        exit "$RC"
        """
      }

    private val (thread, result) =
      Simple_Thread.future("build") { Isabelle_System.bash_env(info.dir.file, env, script) }

    def terminate: Unit = thread.interrupt
    def is_finished: Boolean = result.is_finished

    @volatile private var timeout = false
    private val time = Time.seconds(info.options.real("timeout"))
    private val timer: Option[Timer] =
      if (time.seconds > 0.0) {
        val t = new Timer("build", true)
        t.schedule(new TimerTask { def run = { terminate; timeout = true } }, time.ms)
        Some(t)
      }
      else None

    def join: (String, String, Int) = {
      val (out, err, rc) = result.join
      args_file.delete
      timer.map(_.cancel())

      val err1 =
        if (rc == 130)
          (if (err.isEmpty || err.endsWith("\n")) err else err + "\n") +
          (if (timeout) "*** Timeout\n" else "*** Interrupt\n")
        else err
      (out, err1, rc)
    }
  }


  /* log files and corresponding heaps */

  private val LOG = Path.explode("log")
  private def log(name: String): Path = LOG + Path.basic(name)
  private def log_gz(name: String): Path = log(name).ext("gz")

  private def sources_stamp(digests: List[SHA1.Digest]): String =
    digests.map(_.toString).sorted.mkString("sources: ", " ", "")

  private val no_heap: String = "heap: -"

  private def heap_stamp(heap: Option[Path]): String =
  {
    "heap: " +
      (heap match {
        case Some(path) =>
          val file = path.file
          if (file.isFile) file.length.toString + " " + file.lastModified.toString
          else "-"
        case None => "-"
      })
  }

  private def read_stamps(path: Path): Option[(String, String, String)] =
    if (path.is_file) {
      val stream = new GZIPInputStream (new BufferedInputStream(new FileInputStream(path.file)))
      val reader = new BufferedReader(new InputStreamReader(stream, Standard_System.charset))
      val (s, h1, h2) =
        try { (reader.readLine, reader.readLine, reader.readLine) }
        finally { reader.close }
      if (s != null && s.startsWith("sources: ") &&
          h1 != null && h1.startsWith("heap: ") &&
          h2 != null && h2.startsWith("heap: ")) Some((s, h1, h2))
      else None
    }
    else None


  /* build */

  def build(
    all_sessions: Boolean = false,
    build_heap: Boolean = false,
    clean_build: Boolean = false,
    more_dirs: List[Path] = Nil,
    session_groups: List[String] = Nil,
    max_jobs: Int = 1,
    no_build: Boolean = false,
    build_options: List[String] = Nil,
    system_mode: Boolean = false,
    verbose: Boolean = false,
    sessions: List[String] = Nil): Int =
  {
    val options = (Options.init() /: build_options)(_.define_simple(_))
    val (descendants, tree) =
      find_sessions(options, more_dirs).required(all_sessions, session_groups, sessions)
    val deps = dependencies(verbose, tree)
    val queue = Queue(tree)

    def make_stamp(name: String): String =
      sources_stamp(tree(name).entry_digest :: deps.sources(name))

    val (input_dirs, output_dir, browser_info) =
      if (system_mode) {
        val output_dir = Path.explode("~~/heaps/$ML_IDENTIFIER")
        (List(output_dir), output_dir, Path.explode("~~/browser_info"))
      }
      else {
        val output_dir = Path.explode("$ISABELLE_OUTPUT")
        (output_dir :: Isabelle_System.find_logics_dirs(), output_dir,
         Path.explode("$ISABELLE_BROWSER_INFO"))
      }

    // prepare log dir
    (output_dir + LOG).file.mkdirs()

    // optional cleanup
    if (clean_build) {
      for (name <- descendants) {
        val files =
          List(Path.basic(name), log(name), log_gz(name)).map(output_dir + _).filter(_.is_file)
        if (!files.isEmpty) echo("Cleaning " + name + " ...")
        if (!files.forall(p => p.file.delete)) echo(name + " FAILED to delete")
      }
    }

    // scheduler loop
    case class Result(current: Boolean, heap: String, rc: Int)

    @tailrec def loop(
      pending: Queue,
      running: Map[String, (String, Job)],
      results: Map[String, Result]): Map[String, Result] =
    {
      if (pending.is_empty) results
      else
        running.find({ case (_, (_, job)) => job.is_finished }) match {
          case Some((name, (parent_heap, job))) =>
            // finish job

            val (out, err, rc) = job.join
            echo(Library.trim_line(err))

            val heap =
              if (rc == 0) {
                (output_dir + log(name)).file.delete

                val sources = make_stamp(name)
                val heap = heap_stamp(job.output_path)
                File.write_gzip(output_dir + log_gz(name),
                  sources + "\n" + parent_heap + "\n" + heap + "\n" + out)

                heap
              }
              else {
                (output_dir + Path.basic(name)).file.delete
                (output_dir + log_gz(name)).file.delete

                File.write(output_dir + log(name), out)
                echo(name + " FAILED")
                if (rc != 130) {
                  echo("(see also " + (output_dir + log(name)).file.toString + ")")
                  val lines = split_lines(out)
                  val tail = lines.drop(lines.length - 20 max 0)
                  echo("\n" + cat_lines(tail))
                }

                no_heap
              }
            loop(pending - name, running - name, results + (name -> Result(false, heap, rc)))

          case None if (running.size < (max_jobs max 1)) =>
            // check/start next job
            pending.dequeue(running.isDefinedAt(_)) match {
              case Some((name, info)) =>
                val parent_result =
                  info.parent match {
                    case None => Result(true, no_heap, 0)
                    case Some(parent) => results(parent)
                  }
                val output = output_dir + Path.basic(name)
                val do_output = build_heap || queue.is_inner(name)

                val (current, heap) =
                {
                  input_dirs.find(dir => (dir + log_gz(name)).is_file) match {
                    case Some(dir) =>
                      read_stamps(dir + log_gz(name)) match {
                        case Some((s, h1, h2)) =>
                          val heap = heap_stamp(Some(dir + Path.basic(name)))
                          (s == make_stamp(name) && h1 == parent_result.heap && h2 == heap &&
                            !(do_output && heap == no_heap), heap)
                        case None => (false, no_heap)
                      }
                    case None => (false, no_heap)
                  }
                }
                val all_current = current && parent_result.current

                if (all_current)
                  loop(pending - name, running, results + (name -> Result(true, heap, 0)))
                else if (no_build) {
                  if (verbose) echo("Skipping " + name + " ...")
                  loop(pending - name, running, results + (name -> Result(false, heap, 1)))
                }
                else if (parent_result.rc == 0) {
                  echo((if (do_output) "Building " else "Running ") + name + " ...")
                  val job = new Job(name, info, output, do_output, verbose, browser_info)
                  loop(pending, running + (name -> (parent_result.heap, job)), results)
                }
                else {
                  echo(name + " CANCELLED")
                  loop(pending - name, running, results + (name -> Result(false, heap, 1)))
                }
              case None => sleep(); loop(pending, running, results)
            }
          case None => sleep(); loop(pending, running, results)
        }
    }

    val results =
      if (deps.is_empty) {
        echo("### Nothing to build")
        Map.empty
      }
      else loop(queue, Map.empty, Map.empty)

    val rc = (0 /: results)({ case (rc1, (_, res)) => rc1 max res.rc })
    if (rc != 0 && (verbose || !no_build)) {
      val unfinished =
        (for ((name, res) <- results.iterator if res.rc != 0) yield name).toList.sorted
      echo("Unfinished session(s): " + commas(unfinished))
    }
    rc
  }


  /* command line entry point */

  def main(args: Array[String])
  {
    Command_Line.tool {
      args.toList match {
        case
          Properties.Value.Boolean(all_sessions) ::
          Properties.Value.Boolean(build_heap) ::
          Properties.Value.Boolean(clean_build) ::
          Properties.Value.Int(max_jobs) ::
          Properties.Value.Boolean(no_build) ::
          Properties.Value.Boolean(system_mode) ::
          Properties.Value.Boolean(verbose) ::
          Command_Line.Chunks(more_dirs, session_groups, build_options, sessions) =>
            build(all_sessions, build_heap, clean_build, more_dirs.map(Path.explode),
              session_groups, max_jobs, no_build, build_options, system_mode, verbose, sessions)
        case _ => error("Bad arguments:\n" + cat_lines(args))
      }
    }
  }


  /* static outer syntax */

  // FIXME Symbol.decode!?
  def outer_syntax(session: String): Outer_Syntax =
  {
    val (_, tree) = find_sessions(Options.init(), Nil).required(false, Nil, List(session))
    dependencies(false, tree)(session).syntax
  }
}

