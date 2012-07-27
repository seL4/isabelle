/*  Title:      Pure/System/build.scala
    Author:     Makarius

Build and manage Isabelle sessions.
*/

package isabelle


import java.io.{File => JFile, BufferedInputStream, FileInputStream,
  BufferedReader, InputStreamReader, IOException}
import java.util.zip.GZIPInputStream

import scala.collection.mutable
import scala.annotation.tailrec


object Build
{
  /** session information **/

  object Session
  {
    /* Info */

    sealed case class Info(
      groups: List[String],
      dir: Path,
      parent: Option[String],
      description: String,
      options: Options,
      theories: List[(Options, List[Path])],
      files: List[Path],
      entry_digest: SHA1.Digest)


    /* Queue */

    object Queue
    {
      val empty: Queue = new Queue()
    }

    final class Queue private(graph: Graph[String, Info] = Graph.string)
      extends PartialFunction[String, Info]
    {
      def apply(name: String): Info = graph.get_node(name)
      def isDefinedAt(name: String): Boolean = graph.defined(name)

      def is_inner(name: String): Boolean = !graph.is_maximal(name)

      def is_empty: Boolean = graph.is_empty

      def + (name: String, info: Info): Queue =
        new Queue(
          try { graph.new_node(name, info).add_deps_acyclic(name, info.parent.toList) }
          catch {
            case _: Graph.Duplicate[_] => error("Duplicate session: " + quote(name))
            case exn: Graph.Cycles[_] =>
              error(cat_lines(exn.cycles.map(cycle =>
                "Cyclic session dependency of " +
                  cycle.map(c => quote(c.toString)).mkString(" via "))))
          })

      def - (name: String): Queue = new Queue(graph.del_node(name))

      def required(groups: List[String], names: List[String]): Queue =
      {
        val selected_group = groups.toSet
        val selected_name = names.toSet
        val selected =
          graph.keys.filter(name =>
            selected_name(name) || apply(name).groups.exists(selected_group)).toList
        new Queue(graph.restrict(graph.all_preds(selected).toSet))
      }

      def dequeue(skip: String => Boolean): Option[(String, Info)] =
      {
        val it = graph.entries.dropWhile(
          { case (name, (_, (deps, _))) => !deps.isEmpty || skip(name) })
        if (it.hasNext) { val (name, (info, _)) = it.next; Some((name, info)) }
        else None
      }

      def topological_order: List[(String, Info)] =
        graph.topological_order.map(name => (name, graph.get_node(name)))
    }
  }


  /* parsing */

  private case class Session_Entry(
    base_name: String,
    this_name: Boolean,
    groups: List[String],
    path: Option[String],
    parent: Option[String],
    description: String,
    options: List[Options.Spec],
    theories: List[(List[Options.Spec], List[String])],
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

      val option =
        name ~ opt(keyword("=") ~! name ^^ { case _ ~ x => x }) ^^ { case x ~ y => (x, y) }
      val options = keyword("[") ~> repsep(option, keyword(",")) <~ keyword("]")

      val theories =
        keyword(THEORIES) ~! ((options | success(Nil)) ~ rep1(theory_name)) ^^
          { case _ ~ (x ~ y) => (x, y) }

      ((keyword(SESSION) ~! session_name) ^^ { case _ ~ x => x }) ~
        (keyword("!") ^^^ true | success(false)) ~
        (keyword("(") ~! (rep1(name) <~ keyword(")")) ^^ { case _ ~ x => x } | success(Nil)) ~
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

  private def sessions_root(options: Options, dir: Path, root: JFile, queue: Session.Queue)
    : Session.Queue =
  {
    (queue /: Parser.parse_entries(root))((queue1, entry) =>
      try {
        if (entry.base_name == "") error("Bad session name")

        val full_name =
          if (is_pure(entry.base_name)) {
            if (entry.parent.isDefined) error("Illegal parent session")
            else entry.base_name
          }
          else
            entry.parent match {
              case Some(parent_name) if queue1.isDefinedAt(parent_name) =>
                val full_name =
                  if (entry.this_name) entry.base_name
                  else parent_name + "-" + entry.base_name
                full_name
              case _ => error("Bad parent session")
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
          Session.Info(entry.groups, dir + path, entry.parent, entry.description,
            session_options, theories, files, entry_digest)

        queue1 + (full_name, info)
      }
      catch {
        case ERROR(msg) =>
          error(msg + "\nThe error(s) above occurred in session entry " +
            quote(entry.base_name) + Position.str_of(Position.file(root)))
      })
  }

  private def sessions_dir(options: Options, strict: Boolean, dir: Path, queue: Session.Queue)
    : Session.Queue =
  {
    val root = (dir + ROOT).file
    if (root.isFile) sessions_root(options, dir, root, queue)
    else if (strict) error("Bad session root file: " + quote(root.toString))
    else queue
  }

  private def sessions_catalog(options: Options, dir: Path, catalog: JFile, queue: Session.Queue)
    : Session.Queue =
  {
    val dirs =
      split_lines(File.read(catalog)).filterNot(line => line == "" || line.startsWith("#"))
    (queue /: dirs)((queue1, dir1) =>
      try {
        val dir2 = dir + Path.explode(dir1)
        if (dir2.file.isDirectory) sessions_dir(options, true, dir2, queue1)
        else error("Bad session directory: " + dir2.toString)
      }
      catch {
        case ERROR(msg) =>
          error(msg + "\nThe error(s) above occurred in session catalog " + quote(catalog.toString))
      })
  }

  def find_sessions(options: Options, more_dirs: List[Path],
    all_sessions: Boolean, session_groups: List[String], sessions: List[String]): Session.Queue =
  {
    var queue = Session.Queue.empty

    for (dir <- Isabelle_System.components()) {
      queue = sessions_dir(options, false, dir, queue)

      val catalog = (dir + SESSIONS).file
      if (catalog.isFile)
        queue = sessions_catalog(options, dir, catalog, queue)
    }

    for (dir <- more_dirs) queue = sessions_dir(options, true, dir, queue)

    sessions.filter(name => !queue.isDefinedAt(name)) match {
      case Nil =>
      case bad => error("Undefined session(s): " + commas_quote(bad))
    }

    if (all_sessions) queue else queue.required(session_groups, sessions)
  }



  /** build **/

  private def echo(msg: String) { java.lang.System.out.println(msg) }
  private def sleep(): Unit = Thread.sleep(500)


  /* source dependencies */

  sealed case class Node(
    loaded_theories: Set[String],
    sources: List[(Path, SHA1.Digest)])

  sealed case class Deps(deps: Map[String, Node])
  {
    def sources(name: String): List[SHA1.Digest] = deps(name).sources.map(_._2)
  }

  def dependencies(verbose: Boolean, queue: Session.Queue): Deps =
    Deps((Map.empty[String, Node] /: queue.topological_order)(
      { case (deps, (name, info)) =>
          val preloaded =
            info.parent match {
              case None => Set.empty[String]
              case Some(parent) => deps(parent).loaded_theories
            }
          val thy_info = new Thy_Info(new Thy_Load(preloaded))

          if (verbose) echo("Checking " + name)

          val thy_deps =
            thy_info.dependencies(
              info.theories.map(_._2).flatten.
                map(thy => Document.Node.Name(info.dir + Thy_Load.thy_path(thy))))

          val loaded_theories = preloaded ++ thy_deps.map(_._1.theory)

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
                error(msg + "\nThe error(s) above occurred in session " + quote(name))
            }

          deps + (name -> Node(loaded_theories, sources))
      }))


  /* jobs */

  private class Job(cwd: JFile, env: Map[String, String], script: String, args: String,
    output: Path, do_output: Boolean)
  {
    private val args_file = File.tmp_file("args")
    private val env1 = env + ("ARGS_FILE" -> Isabelle_System.posix_path(args_file.getPath))
    File.write(args_file, args)

    private val (thread, result) =
      Simple_Thread.future("build") { Isabelle_System.bash_env(cwd, env1, script) }

    def terminate: Unit = thread.interrupt
    def is_finished: Boolean = result.is_finished
    def join: (String, String, Int) = { val res = result.join; args_file.delete; res }
    def output_path: Option[Path] = if (do_output) Some(output) else None
  }

  private def start_job(name: String, info: Session.Info, output: Path, do_output: Boolean,
    options: Options, timing: Boolean, verbose: Boolean, browser_info: Path): Job =
  {
    // global browser info dir
    if (options.bool("browser_info") && !(browser_info + Path.explode("index.html")).file.isFile)
    {
      browser_info.file.mkdirs()
      File.copy(Path.explode("~~/lib/logo/isabelle.gif"),
        browser_info + Path.explode("isabelle.gif"))
      File.write(browser_info + Path.explode("index.html"),
        File.read(Path.explode("~~/lib/html/library_index_header.template")) +
        File.read(Path.explode("~~/lib/html/library_index_content.template")) +
        File.read(Path.explode("~~/lib/html/library_index_footer.template")))
    }

    val parent = info.parent.getOrElse("")

    val cwd = info.dir.file
    val env =
      Map("INPUT" -> parent, "TARGET" -> name, "OUTPUT" -> Isabelle_System.standard_path(output))
    val script =
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
    val args_xml =
    {
      import XML.Encode._
          pair(bool, pair(Options.encode, pair(bool, pair(bool, pair(Path.encode, pair(string,
            pair(string, list(pair(Options.encode, list(Path.encode))))))))))(
          (do_output, (options, (timing, (verbose, (browser_info, (parent,
            (name, info.theories))))))))
    }
    new Job(cwd, env, script, YXML.string_of_body(args_xml), output, do_output)
  }


  /* log files and corresponding heaps */

  private val LOG = Path.explode("log")
  private def log(name: String): Path = LOG + Path.basic(name)
  private def log_gz(name: String): Path = log(name).ext("gz")

  private def sources_stamp(digests: List[SHA1.Digest]): String =
    digests.map(_.toString).sorted.mkString("sources: ", " ", "")

  private def heap_stamp(output: Option[Path]): String =
  {
    "heap: " +
      (output match {
        case Some(path) =>
          val file = path.file
          if (file.isFile) file.length.toString + " " + file.lastModified.toString
          else "-"
        case None => "-"
      })
  }

  private def check_stamps(dir: Path, name: String): Option[(String, Boolean)] =
  {
    val file = (dir + log_gz(name)).file
    if (file.isFile) {
      val stream = new GZIPInputStream (new BufferedInputStream(new FileInputStream(file)))
      val reader = new BufferedReader(new InputStreamReader(stream, Standard_System.charset))
      val (s, h) = try { (reader.readLine, reader.readLine) } finally { reader.close }
      if (s != null && s.startsWith("sources: ") && h != null && h.startsWith("heap: ") &&
          h == heap_stamp(Some(dir + Path.basic(name)))) Some((s, h != "heap: -"))
      else None
    }
    else None
  }


  /* build */

  def build(
    all_sessions: Boolean = false,
    build_heap: Boolean = false,
    more_dirs: List[Path] = Nil,
    session_groups: List[String] = Nil,
    max_jobs: Int = 1,
    no_build: Boolean = false,
    build_options: List[String] = Nil,
    system_mode: Boolean = false,
    timing: Boolean = false,
    verbose: Boolean = false,
    sessions: List[String] = Nil): Int =
  {
    val options = (Options.init() /: build_options)(_.define_simple(_))
    val queue = find_sessions(options, more_dirs, all_sessions, session_groups, sessions)
    val deps = dependencies(verbose, queue)

    def make_stamp(name: String): String =
      sources_stamp(queue(name).entry_digest :: deps.sources(name))

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

    // scheduler loop
    @tailrec def loop(
      pending: Session.Queue,
      running: Map[String, Job],
      results: Map[String, (Boolean, Int)]): Map[String, (Boolean, Int)] =
    {
      if (pending.is_empty) results
      else if (running.exists({ case (_, job) => job.is_finished }))
      { // finish job
        val (name, job) = running.find({ case (_, job) => job.is_finished }).get

        val (out, err, rc) = job.join
        echo(Library.trim_line(err))

        if (rc == 0) {
          val sources = make_stamp(name)
          val heap = heap_stamp(job.output_path)
          File.write_gzip(output_dir + log_gz(name), sources + "\n" + heap + "\n" + out)
        }
        else {
          File.write(output_dir + log(name), out)
          echo(name + " FAILED")
          echo("(see also " + log(name).file.toString + ")")
          val lines = split_lines(out)
          val tail = lines.drop(lines.length - 20 max 0)
          echo("\n" + cat_lines(tail))
        }
        loop(pending - name, running - name, results + (name -> (false, rc)))
      }
      else if (running.size < (max_jobs max 1))
      { // check/start next job
        pending.dequeue(running.isDefinedAt(_)) match {
          case Some((name, info)) =>
            val parent_result = info.parent.map(results(_))
            val parent_current = parent_result.forall(_._1)
            val parent_ok = parent_result.forall(_._2 == 0)

            val output = output_dir + Path.basic(name)
            val do_output = build_heap || queue.is_inner(name)

            val current =
            {
              input_dirs.find(dir => (dir + log_gz(name)).file.isFile) match {
                case Some(dir) =>
                  check_stamps(dir, name) match {
                    case Some((s, h)) => s == make_stamp(name) && (h || !do_output)
                    case None => false
                  }
                case None => false
              }
            }
            val all_current = current && parent_current

            if (all_current)
              loop(pending - name, running, results + (name -> (true, 0)))
            else if (no_build)
              loop(pending - name, running, results + (name -> (false, 1)))
            else if (parent_ok) {
              echo((if (do_output) "Building " else "Running ") + name + " ...")
              val job =
                start_job(name, info, output, do_output, info.options, timing, verbose, browser_info)
              loop(pending, running + (name -> job), results)
            }
            else {
              echo(name + " CANCELLED")
              loop(pending - name, running, results + (name -> (false, 1)))
            }
          case None => sleep(); loop(pending, running, results)
        }
      }
      else { sleep(); loop(pending, running, results) }
    }

    val results = loop(queue, Map.empty, Map.empty)
    val rc = (0 /: results)({ case (rc1, (_, (_, rc2))) => rc1 max rc2 })
    if (rc != 0 && (verbose || !no_build)) {
      val unfinished = (for ((name, r) <- results.iterator if r != 0) yield name).toList.sorted
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
          Properties.Value.Int(max_jobs) ::
          Properties.Value.Boolean(no_build) ::
          Properties.Value.Boolean(system_mode) ::
          Properties.Value.Boolean(timing) ::
          Properties.Value.Boolean(verbose) ::
          Command_Line.Chunks(more_dirs, session_groups, build_options, sessions) =>
            build(all_sessions, build_heap, more_dirs.map(Path.explode), session_groups,
              max_jobs, no_build, build_options, system_mode, timing, verbose, sessions)
        case _ => error("Bad arguments:\n" + cat_lines(args))
      }
    }
  }
}

