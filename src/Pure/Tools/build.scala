/*  Title:      Pure/Tools/build.scala
    Author:     Makarius
    Options:    :folding=explicit:collapseFolds=1:

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
  /** progress context **/

  class Progress
  {
    def echo(msg: String) {}
    def theory(session: String, theory: String) {}
    def stopped: Boolean = false
  }

  object Ignore_Progress extends Progress

  class Console_Progress(verbose: Boolean) extends Progress
  {
    override def echo(msg: String) { java.lang.System.out.println(msg) }
    override def theory(session: String, theory: String): Unit =
      if (verbose) echo(session + ": theory " + theory)
  }



  /** session information **/

  // external version
  sealed case class Session_Entry(
    pos: Position.T,
    name: String,
    groups: List[String],
    path: String,
    parent: Option[String],
    description: String,
    options: List[Options.Spec],
    theories: List[(List[Options.Spec], List[String])],
    files: List[String])

  // internal version
  sealed case class Session_Info(
    select: Boolean,
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

  def session_info(options: Options, select: Boolean, dir: Path, entry: Session_Entry)
      : (String, Session_Info) =
    try {
      val name = entry.name

      if (name == "") error("Bad session name")
      if (is_pure(name) && entry.parent.isDefined) error("Illegal parent session")
      if (!is_pure(name) && !entry.parent.isDefined) error("Missing parent session")

      val session_options = options ++ entry.options

      val theories =
        entry.theories.map({ case (opts, thys) =>
          (session_options ++ opts, thys.map(Path.explode(_))) })
      val files = entry.files.map(Path.explode(_))
      val entry_digest = SHA1.digest((name, entry.parent, entry.options, entry.theories).toString)

      val info =
        Session_Info(select, entry.pos, entry.groups, dir + Path.explode(entry.path),
          entry.parent, entry.description, session_options, theories, files, entry_digest)

      (name, info)
    }
    catch {
      case ERROR(msg) =>
        error(msg + "\nThe error(s) above occurred in session entry " +
          quote(entry.name) + Position.here(entry.pos))
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
              error("Duplicate session " + quote(name) + Position.here(info.pos))
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
                    quote(name) + Position.here(info.pos))

                try { graph.add_edge_acyclic(parent, name) }
                catch {
                  case exn: Graph.Cycles[_] =>
                    error(cat_lines(exn.cycles.map(cycle =>
                      "Cyclic session dependency of " +
                        cycle.map(c => quote(c.toString)).mkString(" via "))) +
                          Position.here(info.pos))
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

    def selection(requirements: Boolean, all_sessions: Boolean,
      session_groups: List[String], sessions: List[String]): (List[String], Session_Tree) =
    {
      val bad_sessions = sessions.filterNot(isDefinedAt(_))
      if (!bad_sessions.isEmpty) error("Undefined session(s): " + commas_quote(bad_sessions))

      val pre_selected =
      {
        if (all_sessions) graph.keys.toList
        else {
          val select_group = session_groups.toSet
          val select = sessions.toSet
          (for {
            (name, (info, _)) <- graph.entries
            if info.select || select(name) || apply(name).groups.exists(select_group)
          } yield name).toList
        }
      }
      val selected =
        if (requirements) (graph.all_preds(pre_selected).toSet -- pre_selected).toList
        else pre_selected

      val tree1 = new Session_Tree(graph.restrict(graph.all_preds(selected).toSet))
      (selected, tree1)
    }

    def topological_order: List[(String, Session_Info)] =
      graph.topological_order.map(name => (name, apply(name)))

    override def toString: String = graph.entries.map(_._1).toList.sorted.mkString(",")
  }


  /* parser */

  private val SESSION = "session"
  private val IN = "in"
  private val DESCRIPTION = "description"
  private val OPTIONS = "options"
  private val THEORIES = "theories"
  private val FILES = "files"

  lazy val root_syntax =
    Outer_Syntax.init() + "(" + ")" + "+" + "," + "=" + "[" + "]" +
      (SESSION, Keyword.THY_DECL) + IN + DESCRIPTION + OPTIONS + THEORIES + FILES

  private object Parser extends Parse.Parser
  {
    def session_entry(pos: Position.T): Parser[Session_Entry] =
    {
      val session_name = atom("session name", _.is_name)

      val option =
        name ~ opt(keyword("=") ~! name ^^ { case _ ~ x => x }) ^^ { case x ~ y => (x, y) }
      val options = keyword("[") ~> rep1sep(option, keyword(",")) <~ keyword("]")

      val theories =
        keyword(THEORIES) ~! ((options | success(Nil)) ~ rep(theory_name)) ^^
          { case _ ~ (x ~ y) => (x, y) }

      command(SESSION) ~!
        (session_name ~
          ((keyword("(") ~! (rep1(name) <~ keyword(")")) ^^ { case _ ~ x => x }) | success(Nil)) ~
          ((keyword(IN) ~! path ^^ { case _ ~ x => x }) | success(".")) ~
          (keyword("=") ~!
            (opt(session_name ~! keyword("+") ^^ { case x ~ _ => x }) ~
              ((keyword(DESCRIPTION) ~! text ^^ { case _ ~ x => x }) | success("")) ~
              ((keyword(OPTIONS) ~! options ^^ { case _ ~ x => x }) | success(Nil)) ~
              rep1(theories) ~
              ((keyword(FILES) ~! rep1(path) ^^ { case _ ~ x => x }) | success(Nil))))) ^^
        { case _ ~ (a ~ b ~ c ~ (_ ~ (d ~ e ~ f ~ g ~ h))) =>
            Session_Entry(pos, a, b, c, d, e, f, g, h) }
    }

    def parse_entries(root: Path): List[Session_Entry] =
    {
      val toks = root_syntax.scan(File.read(root))
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

  def find_sessions(options: Options, more_dirs: List[(Boolean, Path)]): Session_Tree =
  {
    def find_dir(select: Boolean, dir: Path): List[(String, Session_Info)] =
      find_root(select, dir) ::: find_roots(select, dir)

    def find_root(select: Boolean, dir: Path): List[(String, Session_Info)] =
    {
      val root = dir + ROOT
      if (root.is_file) Parser.parse_entries(root).map(session_info(options, select, dir, _))
      else Nil
    }

    def find_roots(select: Boolean, dir: Path): List[(String, Session_Info)] =
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
          info <- find_dir(select, dir1)
        } yield info
      }
      else Nil
    }

    val default_dirs = Isabelle_System.components().filter(is_session_dir(_)).map((false, _))

    more_dirs foreach { case (_, dir) => check_session_dir(dir) }

    Session_Tree(
      for {
        (select, dir) <- default_dirs ::: more_dirs
        info <- find_dir(select, dir)
      } yield info)
  }



  /** build **/

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


  /* source dependencies and static content */

  sealed case class Session_Content(
    loaded_theories: Set[String],
    syntax: Outer_Syntax,
    sources: List[(Path, SHA1.Digest)],
    errors: List[String])
  {
    def check_errors: Session_Content =
    {
      if (errors.isEmpty) this
      else error(cat_lines(errors))
    }
  }

  sealed case class Deps(deps: Map[String, Session_Content])
  {
    def is_empty: Boolean = deps.isEmpty
    def apply(name: String): Session_Content = deps(name)
    def sources(name: String): List[SHA1.Digest] = deps(name).sources.map(_._2)
  }

  def dependencies(progress: Build.Progress, inlined_files: Boolean,
      verbose: Boolean, list_files: Boolean, tree: Session_Tree): Deps =
    Deps((Map.empty[String, Session_Content] /: tree.topological_order)(
      { case (deps, (name, info)) =>
          val (preloaded, parent_syntax, parent_errors) =
            info.parent match {
              case None =>
                (Set.empty[String], Outer_Syntax.init_pure(), Nil)
              case Some(parent_name) =>
                val parent = deps(parent_name)
                (parent.loaded_theories, parent.syntax, parent.errors)
            }
          val thy_info = new Thy_Info(new Thy_Load(preloaded, parent_syntax))

          if (verbose || list_files) {
            val groups =
              if (info.groups.isEmpty) ""
              else info.groups.mkString(" (", " ", ")")
            progress.echo("Session " + name + groups)
          }

          val thy_deps =
            thy_info.dependencies(inlined_files,
              info.theories.map(_._2).flatten.
                map(thy => Thy_Load.path_node_name(info.dir + Thy_Load.thy_path(thy))))

          val loaded_theories = thy_deps.loaded_theories
          val syntax = thy_deps.make_syntax

          val all_files =
            (thy_deps.deps.map({ case dep =>
              val thy = Path.explode(dep.name.node)
              val uses = dep.join_header.uses.map(p =>
                Path.explode(dep.name.dir) + Path.explode(p._1))
              thy :: uses
            }).flatten ::: info.files.map(file => info.dir + file)).map(_.expand)

          if (list_files)
            progress.echo(cat_lines(all_files.map(_.implode).sorted.map("  " + _)))

          val sources =
            try { all_files.map(p => (p, SHA1.digest(p.file))) }
            catch {
              case ERROR(msg) =>
                error(msg + "\nThe error(s) above occurred in session " +
                  quote(name) + Position.here(info.pos))
            }
          val errors = parent_errors ::: thy_deps.deps.map(dep => dep.join_header.errors).flatten

          deps + (name -> Session_Content(loaded_theories, syntax, sources, errors))
      }))

  def session_content(inlined_files: Boolean, dirs: List[Path], session: String): Session_Content =
  {
    val options = Options.init()
    val (_, tree) =
      find_sessions(options, dirs.map((false, _))).selection(false, false, Nil, List(session))
    dependencies(Build.Ignore_Progress, inlined_files, false, false, tree)(session)
  }

  def outer_syntax(session: String): Outer_Syntax =
    session_content(false, Nil, session).check_errors.syntax


  /* jobs */

  private class Job(progress: Build.Progress,
    name: String, val info: Session_Info, output: Path, do_output: Boolean,
    verbose: Boolean, browser_info: Path)
  {
    // global browser info dir
    if (info.options.bool("browser_info") && !(browser_info + Path.explode("index.html")).is_file)
    {
      Isabelle_System.mkdirs(browser_info)
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
          Isabelle_System.posix_path(args_file))

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
      Simple_Thread.future("build") {
        Isabelle_System.bash_env(info.dir.file, env, script,
          out_progress = (line: String) =>
            Library.try_unprefix("\floading_theory = ", line) match {
              case Some(theory) => progress.theory(name, theory)
              case None =>
            })
      }

    def terminate: Unit = thread.interrupt
    def is_finished: Boolean = result.is_finished

    @volatile private var timeout = false
    private val time = info.options.seconds("timeout")
    private val timer: Option[Timer] =
      if (time.seconds > 0.0) {
        val t = new Timer("build", true)
        t.schedule(new TimerTask { def run = { terminate; timeout = true } }, time.ms)
        Some(t)
      }
      else None

    def join: Isabelle_System.Bash_Result =
    {
      val res = result.join

      args_file.delete
      timer.map(_.cancel())

      if (res.rc == 130)
        res.add_err(if (timeout) "*** Timeout" else "*** Interrupt")
      else res
    }
  }


  /* inlined properties (YXML) */

  object Props
  {
    def parse(text: String): Properties.T = XML.Decode.properties(YXML.parse_body(text))

    def parse_lines(prefix: String, lines: List[String]): List[Properties.T] =
      for (line <- lines; s <- Library.try_unprefix(prefix, line)) yield parse(s)

    def find_parse_line(prefix: String, lines: List[String]): Option[Properties.T] =
      lines.find(_.startsWith(prefix)).map(line => parse(line.substring(prefix.length)))
  }


  /* log files */

  private val LOG = Path.explode("log")
  private def log(name: String): Path = LOG + Path.basic(name)
  private def log_gz(name: String): Path = log(name).ext("gz")

  private val SESSION_NAME = "\fSession.name = "
  private val SESSION_PARENT_PATH = "\fSession.parent_path = "


  sealed case class Log_Info(
    name: String, stats: List[Properties.T], tasks: List[Properties.T], timing: Properties.T)

  def parse_log(text: String): Log_Info =
  {
    val lines = split_lines(text)
    val name =
      lines.find(_.startsWith(SESSION_NAME)).map(_.substring(SESSION_NAME.length)) getOrElse ""
    val stats = Props.parse_lines("\fML_statistics = ", lines)
    val tasks = Props.parse_lines("\ftask_statistics = ", lines)
    val timing = Props.find_parse_line("\fTiming = ", lines) getOrElse Nil
    Log_Info(name, stats, tasks, timing)
  }


  /* sources and heaps */

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
      val reader = new BufferedReader(new InputStreamReader(stream, UTF8.charset))
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
    progress: Build.Progress,
    options: Options,
    requirements: Boolean = false,
    all_sessions: Boolean = false,
    build_heap: Boolean = false,
    clean_build: Boolean = false,
    more_dirs: List[(Boolean, Path)] = Nil,
    session_groups: List[String] = Nil,
    max_jobs: Int = 1,
    list_files: Boolean = false,
    no_build: Boolean = false,
    system_mode: Boolean = false,
    verbose: Boolean = false,
    sessions: List[String] = Nil): Int =
  {
    val full_tree = find_sessions(options, more_dirs)
    val (selected, selected_tree) =
      full_tree.selection(requirements, all_sessions, session_groups, sessions)

    val deps = dependencies(progress, true, verbose, list_files, selected_tree)
    val queue = Queue(selected_tree)

    def make_stamp(name: String): String =
      sources_stamp(selected_tree(name).entry_digest :: deps.sources(name))

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
    Isabelle_System.mkdirs(output_dir + LOG)

    // optional cleanup
    if (clean_build) {
      for (name <- full_tree.graph.all_succs(selected)) {
        val files =
          List(Path.basic(name), log(name), log_gz(name)).map(output_dir + _).filter(_.is_file)
        if (!files.isEmpty) progress.echo("Cleaning " + name + " ...")
        if (!files.forall(p => p.file.delete)) progress.echo(name + " FAILED to delete")
      }
    }

    // scheduler loop
    case class Result(current: Boolean, parent_path: Option[String], heap: String, rc: Int)

    def sleep(): Unit = Thread.sleep(500)

    @tailrec def loop(
      pending: Queue,
      running: Map[String, (String, Job)],
      results: Map[String, Result]): Map[String, Result] =
    {
      if (pending.is_empty) results
      else if (progress.stopped) {
        for ((_, (_, job)) <- running) job.terminate
        sleep(); loop(pending, running, results)
      }
      else
        running.find({ case (_, (_, job)) => job.is_finished }) match {
          case Some((name, (parent_heap, job))) =>
            //{{{ finish job

            val res = job.join
            progress.echo(res.err)

            val (parent_path, heap) =
              if (res.rc == 0) {
                (output_dir + log(name)).file.delete

                val sources = make_stamp(name)
                val heap = heap_stamp(job.output_path)
                File.write_gzip(output_dir + log_gz(name),
                  sources + "\n" + parent_heap + "\n" + heap + "\n" + res.out)

                val parent_path =
                  if (job.info.options.bool("browser_info"))
                    res.out_lines.find(_.startsWith(SESSION_PARENT_PATH))
                      .map(_.substring(SESSION_PARENT_PATH.length))
                  else None

                (parent_path, heap)
              }
              else {
                (output_dir + Path.basic(name)).file.delete
                (output_dir + log_gz(name)).file.delete

                File.write(output_dir + log(name), res.out)
                progress.echo(name + " FAILED")
                if (res.rc != 130) {
                  progress.echo("(see also " + (output_dir + log(name)).file.toString + ")")
                  val lines = res.out_lines.filterNot(_.startsWith("\f"))
                  val tail = lines.drop(lines.length - 20 max 0)
                  progress.echo("\n" + cat_lines(tail))
                }

                (None, no_heap)
              }
            loop(pending - name, running - name,
              results + (name -> Result(false, parent_path, heap, res.rc)))
            //}}}
          case None if (running.size < (max_jobs max 1)) =>
            //{{{ check/start next job
            pending.dequeue(running.isDefinedAt(_)) match {
              case Some((name, info)) =>
                val parent_result =
                  info.parent match {
                    case None => Result(true, None, no_heap, 0)
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
                  loop(pending - name, running, results + (name -> Result(true, None, heap, 0)))
                else if (no_build) {
                  if (verbose) progress.echo("Skipping " + name + " ...")
                  loop(pending - name, running, results + (name -> Result(false, None, heap, 1)))
                }
                else if (parent_result.rc == 0) {
                  progress.echo((if (do_output) "Building " else "Running ") + name + " ...")
                  val job = new Job(progress, name, info, output, do_output, verbose, browser_info)
                  loop(pending, running + (name -> (parent_result.heap, job)), results)
                }
                else {
                  progress.echo(name + " CANCELLED")
                  loop(pending - name, running, results + (name -> Result(false, None, heap, 1)))
                }
              case None => sleep(); loop(pending, running, results)
            }
            ///}}}
          case None => sleep(); loop(pending, running, results)
        }
    }

    val results =
      if (deps.is_empty) {
        progress.echo("### Nothing to build")
        Map.empty[String, Result]
      }
      else loop(queue, Map.empty, Map.empty)

    val session_entries =
      (for ((name, res) <- results.iterator if res.parent_path.isDefined)
        yield (res.parent_path.get, name)).toList.groupBy(_._1).map(
          { case (p, es) => (p, es.map(_._2).sorted) })
    for ((p, names) <- session_entries)
      Present.update_index(browser_info + Path.explode(p), names)

    val rc = (0 /: results)({ case (rc1, (_, res)) => rc1 max res.rc })
    if (rc != 0 && (verbose || !no_build)) {
      val unfinished =
        (for ((name, res) <- results.iterator if res.rc != 0) yield name).toList
          .sorted(scala.math.Ordering.String)  // FIXME scala-2.10.0-RC1
      progress.echo("Unfinished session(s): " + commas(unfinished))
    }
    rc
  }


  /* command line entry point */

  def main(args: Array[String])
  {
    Command_Line.tool {
      args.toList match {
        case
          Properties.Value.Boolean(requirements) ::
          Properties.Value.Boolean(all_sessions) ::
          Properties.Value.Boolean(build_heap) ::
          Properties.Value.Boolean(clean_build) ::
          Properties.Value.Int(max_jobs) ::
          Properties.Value.Boolean(list_files) ::
          Properties.Value.Boolean(no_build) ::
          Properties.Value.Boolean(system_mode) ::
          Properties.Value.Boolean(verbose) ::
          Command_Line.Chunks(select_dirs, include_dirs, session_groups, build_options, sessions) =>
            val options = (Options.init() /: build_options)(_ + _)
            val dirs =
              select_dirs.map(d => (true, Path.explode(d))) :::
              include_dirs.map(d => (false, Path.explode(d)))
            build(new Build.Console_Progress(verbose), options, requirements, all_sessions,
              build_heap, clean_build, dirs, session_groups, max_jobs, list_files, no_build,
              system_mode, verbose, sessions)
        case _ => error("Bad arguments:\n" + cat_lines(args))
      }
    }
  }
}

