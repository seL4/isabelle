/*  Title:      Pure/Tools/build.scala
    Author:     Makarius
    Options:    :folding=explicit:

Build and manage Isabelle sessions.
*/

package isabelle


import java.io.{BufferedInputStream, FileInputStream,
  BufferedReader, InputStreamReader, IOException}
import java.util.zip.GZIPInputStream

import scala.collection.SortedSet
import scala.collection.mutable
import scala.annotation.tailrec


object Build
{
  /** auxiliary **/

  /* queue */

  private object Queue
  {
    def apply(tree: Sessions.Tree, load_timings: String => (List[Properties.T], Double)): Queue =
    {
      val graph = tree.graph
      val sessions = graph.keys

      val timings = Par_List.map((name: String) => (name, load_timings(name)), sessions)
      val command_timings =
        Map(timings.map({ case (name, (ts, _)) => (name, ts) }): _*).withDefaultValue(Nil)
      val session_timing =
        Map(timings.map({ case (name, (_, t)) => (name, t) }): _*).withDefaultValue(0.0)

      def outdegree(name: String): Int = graph.imm_succs(name).size

      object Ordering extends scala.math.Ordering[String]
      {
        def compare_timing(name1: String, name2: String): Int =
        {
          val t1 = session_timing(name1)
          val t2 = session_timing(name2)
          if (t1 == 0.0 || t2 == 0.0) 0
          else t1 compare t2
        }

        def compare(name1: String, name2: String): Int =
          outdegree(name2) compare outdegree(name1) match {
            case 0 =>
              compare_timing(name2, name1) match {
                case 0 =>
                  tree(name2).timeout compare tree(name1).timeout match {
                    case 0 => name1 compare name2
                    case ord => ord
                  }
                case ord => ord
              }
            case ord => ord
          }
      }

      new Queue(graph, SortedSet(sessions: _*)(Ordering), command_timings)
    }
  }

  private final class Queue private(
    graph: Graph[String, Sessions.Info],
    order: SortedSet[String],
    val command_timings: String => List[Properties.T])
  {
    def is_inner(name: String): Boolean = !graph.is_maximal(name)

    def is_empty: Boolean = graph.is_empty

    def - (name: String): Queue =
      new Queue(graph.del_node(name),
        order - name,  // FIXME scala-2.10.0 TreeSet problem!?
        command_timings)

    def dequeue(skip: String => Boolean): Option[(String, Sessions.Info)] =
    {
      val it = order.iterator.dropWhile(name =>
        skip(name)
          || !graph.defined(name)  // FIXME scala-2.10.0 TreeSet problem!?
          || !graph.is_minimal(name))
      if (it.hasNext) { val name = it.next; Some((name, graph.get_node(name))) }
      else None
    }
  }


  /* source dependencies and static content */

  sealed case class Session_Content(
    loaded_theories: Set[String],
    known_theories: Map[String, Document.Node.Name],
    keywords: Thy_Header.Keywords,
    syntax: Outer_Syntax,
    sources: List[(Path, SHA1.Digest)],
    session_graph: Graph_Display.Graph)

  sealed case class Deps(deps: Map[String, Session_Content])
  {
    def is_empty: Boolean = deps.isEmpty
    def apply(name: String): Session_Content = deps(name)
    def sources(name: String): List[SHA1.Digest] = deps(name).sources.map(_._2)
  }

  def dependencies(
      progress: Progress = Ignore_Progress,
      inlined_files: Boolean = false,
      verbose: Boolean = false,
      list_files: Boolean = false,
      check_keywords: Set[String] = Set.empty,
      tree: Sessions.Tree): Deps =
    Deps((Map.empty[String, Session_Content] /: tree.topological_order)(
      { case (deps, (name, info)) =>
          if (progress.stopped) throw Exn.Interrupt()

          try {
            val (loaded_theories0, known_theories0, syntax0) =
              info.parent.map(deps(_)) match {
                case None =>
                  (Set.empty[String], Map.empty[String, Document.Node.Name],
                    Thy_Header.bootstrap_syntax)
                case Some(parent) =>
                  (parent.loaded_theories, parent.known_theories, parent.syntax)
              }
            val resources = new Resources(loaded_theories0, known_theories0, syntax0)
            val thy_info = new Thy_Info(resources)

            if (verbose || list_files) {
              val groups =
                if (info.groups.isEmpty) ""
                else info.groups.mkString(" (", " ", ")")
              progress.echo("Session " + info.chapter + "/" + name + groups)
            }

            val thy_deps =
            {
              val root_theories =
                info.theories.flatMap({
                  case (global, _, thys) =>
                    thys.map(thy =>
                      (resources.node_name(
                        if (global) "" else name, info.dir + Resources.thy_path(thy)), info.pos))
                })
              val thy_deps = thy_info.dependencies(name, root_theories)

              thy_deps.errors match {
                case Nil => thy_deps
                case errs => error(cat_lines(errs))
              }
            }

            val known_theories =
              (known_theories0 /: thy_deps.deps)({ case (known, dep) =>
                val name = dep.name
                known.get(name.theory) match {
                  case Some(name1) if name != name1 =>
                    error("Duplicate theory " + quote(name.node) + " vs. " + quote(name1.node))
                  case _ =>
                    known + (name.theory -> name) + (Long_Name.base_name(name.theory) -> name)
                }
              })

            val loaded_theories = thy_deps.loaded_theories
            val keywords = thy_deps.keywords
            val syntax = thy_deps.syntax.asInstanceOf[Outer_Syntax]

            val theory_files = thy_deps.deps.map(dep => Path.explode(dep.name.node))
            val loaded_files = if (inlined_files) thy_deps.loaded_files else Nil

            val all_files =
              (theory_files ::: loaded_files :::
                info.files.map(file => info.dir + file) :::
                info.document_files.map(file => info.dir + file._1 + file._2)).map(_.expand)

            if (list_files)
              progress.echo(cat_lines(all_files.map(_.implode).sorted.map("  " + _)))

            if (check_keywords.nonEmpty)
              Check_Keywords.check_keywords(progress, syntax.keywords, check_keywords, theory_files)

            val sources = all_files.map(p => (p, SHA1.digest(p.file)))

            val session_graph =
              Present.session_graph(info.parent getOrElse "", loaded_theories0, thy_deps.deps)

            val content =
              Session_Content(loaded_theories, known_theories, keywords, syntax,
                sources, session_graph)
            deps + (name -> content)
          }
          catch {
            case ERROR(msg) =>
              cat_error(msg, "The error(s) above occurred in session " +
                quote(name) + Position.here(info.pos))
          }
      }))

  def session_dependencies(
    options: Options,
    inlined_files: Boolean,
    dirs: List[Path],
    sessions: List[String]): Deps =
  {
    val (_, tree) = Sessions.load(options, dirs = dirs).selection(sessions = sessions)
    dependencies(inlined_files = inlined_files, tree = tree)
  }

  def session_content(
    options: Options,
    inlined_files: Boolean,
    dirs: List[Path],
    session: String): Session_Content =
  {
    session_dependencies(options, inlined_files, dirs, List(session))(session)
  }

  def outer_syntax(options: Options, session: String): Outer_Syntax =
    session_content(options, false, Nil, session).syntax


  /* jobs */

  private class Job(progress: Progress, name: String, val info: Sessions.Info, tree: Sessions.Tree,
    store: Sessions.Store, do_output: Boolean, verbose: Boolean,
    session_graph: Graph_Display.Graph, command_timings: List[Properties.T])
  {
    val output = store.output_dir + Path.basic(name)
    def output_path: Option[Path] = if (do_output) Some(output) else None
    def output_save_state: String =
      if (do_output)
        "PolyML.SaveState.saveChild (" + ML_Syntax.print_string_raw(File.platform_path(output)) +
          ", List.length (PolyML.SaveState.showHierarchy ()))"
      else ""
    output.file.delete

    private val parent = info.parent.getOrElse("")

    private val graph_file = Isabelle_System.tmp_file("session_graph", "pdf")
    try { isabelle.graphview.Graph_File.write(info.options, graph_file, session_graph) }
    catch { case ERROR(_) => /*error should be exposed in ML*/ }

    private val env =
      Isabelle_System.settings() +
        ("ISABELLE_ML_DEBUGGER" -> info.options.bool("ML_debugger").toString)

    private val future_result: Future[Process_Result] =
      Future.thread("build") {
        val process =
          if (Sessions.is_pure(name)) {
            val eval =
              "Command_Line.tool0 (fn () => (Session.finish (); Options.reset_default ();" +
              " Session.shutdown (); ML_Heap.share_common_data (); " + output_save_state + "));"
            ML_Process(info.options, "RAW_ML_SYSTEM", List("--use", "ROOT.ML", "--eval", eval),
              cwd = info.dir.file, env = env, tree = Some(tree), store = store)
          }
          else {
            val args_file = Isabelle_System.tmp_file("build")
            File.write(args_file, YXML.string_of_body(
                {
                  val theories = info.theories.map(x => (x._2, x._3))
                  import XML.Encode._
                  pair(list(pair(string, int)), pair(list(properties), pair(bool, pair(bool,
                    pair(Path.encode, pair(list(pair(Path.encode, Path.encode)), pair(string,
                    pair(string, pair(string, pair(string,
                    list(pair(Options.encode, list(Path.encode)))))))))))))(
                  (Symbol.codes, (command_timings, (do_output, (verbose,
                    (store.browser_info, (info.document_files, (File.standard_path(graph_file),
                    (parent, (info.chapter, (name,
                    theories)))))))))))
                }))
            val eval =
              "Command_Line.tool0 (fn () => (" +
              "Build.build " + ML_Syntax.print_string_raw(File.standard_path(args_file)) +
              (if (do_output) "; ML_Heap.share_common_data (); " + output_save_state
               else "") + "));"
            ML_Process(info.options, parent, List("--eval", eval), cwd = info.dir.file,
              env = env, tree = Some(tree), store = store, cleanup = () => args_file.delete)
          }
        process.result(
          progress_stdout = (line: String) =>
            Library.try_unprefix("\floading_theory = ", line) match {
              case Some(theory) => progress.theory(name, theory)
              case None =>
            },
          progress_limit =
            info.options.int("process_output_limit") match {
              case 0 => None
              case m => Some(m * 1000000L)
            },
          strict = false)
      }

    def terminate: Unit = future_result.cancel
    def is_finished: Boolean = future_result.is_finished

    @volatile private var was_timeout = false
    private val timeout_request: Option[Event_Timer.Request] =
    {
      if (info.timeout > Time.zero)
        Some(Event_Timer.request(Time.now() + info.timeout) { terminate; was_timeout = true })
      else None
    }

    def join: Process_Result =
    {
      val result = future_result.join

      if (result.ok && !Sessions.is_pure(name))
        Present.finish(progress, store.browser_info, graph_file, info, name)

      graph_file.delete
      timeout_request.foreach(_.cancel)

      if (result.interrupted) {
        if (was_timeout) result.error(Output.error_text("Timeout")).was_timeout
        else result.error(Output.error_text("Interrupt"))
      }
      else result
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

  private val SESSION_NAME = "\fSession.name = "

  sealed case class Log_Info(
    name: String,
    stats: List[Properties.T],
    tasks: List[Properties.T],
    command_timings: List[Properties.T],
    session_timing: Properties.T)

  def parse_log(full_stats: Boolean, text: String): Log_Info =
  {
    val lines = split_lines(text)
    val xml_cache = new XML.Cache()
    def parse_lines(prfx: String): List[Properties.T] =
      Props.parse_lines(prfx, lines).map(xml_cache.props(_))

    val name =
      lines.find(_.startsWith(SESSION_NAME)).map(_.substring(SESSION_NAME.length)) getOrElse ""
    val stats = if (full_stats) parse_lines("\fML_statistics = ") else Nil
    val tasks = if (full_stats) parse_lines("\ftask_statistics = ") else Nil
    val command_timings = parse_lines("\fcommand_timing = ")
    val session_timing = Props.find_parse_line("\fTiming = ", lines) getOrElse Nil
    Log_Info(name, stats, tasks, command_timings, session_timing)
  }


  /* sources and heaps */

  private val SOURCES = "sources: "
  private val INPUT_HEAP = "input_heap: "
  private val OUTPUT_HEAP = "output_heap: "
  private val LOG_START = "log:"
  private val line_prefixes = List(SOURCES, INPUT_HEAP, OUTPUT_HEAP, LOG_START)

  private def sources_stamp(digests: List[SHA1.Digest]): String =
    digests.map(_.toString).sorted.mkString(SOURCES, " ", "")

  private def read_stamps(path: Path): Option[(String, List[String], List[String])] =
    if (path.is_file) {
      val stream = new GZIPInputStream(new BufferedInputStream(new FileInputStream(path.file)))
      val reader = new BufferedReader(new InputStreamReader(stream, UTF8.charset))
      val lines =
      {
        val lines = new mutable.ListBuffer[String]
        try {
          var finished = false
          while (!finished) {
            val line = reader.readLine
            if (line != null && line_prefixes.exists(line.startsWith(_)))
              lines += line
            else finished = true
          }
        }
        finally { reader.close }
        lines.toList
      }

      if (!lines.isEmpty && lines.last.startsWith(LOG_START)) {
        lines.find(_.startsWith(SOURCES)).map(s =>
          (s, lines.filter(_.startsWith(INPUT_HEAP)), lines.filter(_.startsWith(OUTPUT_HEAP))))
      }
      else None
    }
    else None



  /** build_results **/

  class Build_Results private [Build](results: Map[String, Option[Process_Result]])
  {
    def sessions: Set[String] = results.keySet
    def cancelled(name: String): Boolean = results(name).isEmpty
    def apply(name: String): Process_Result = results(name).getOrElse(Process_Result(1))
    val rc = (0 /: results.iterator.map({ case (_, Some(r)) => r.rc case (_, None) => 1 }))(_ max _)

    override def toString: String = rc.toString
  }

  def build_results(
    options: Options,
    progress: Progress = Ignore_Progress,
    requirements: Boolean = false,
    all_sessions: Boolean = false,
    build_heap: Boolean = false,
    clean_build: Boolean = false,
    dirs: List[Path] = Nil,
    select_dirs: List[Path] = Nil,
    exclude_session_groups: List[String] = Nil,
    session_groups: List[String] = Nil,
    max_jobs: Int = 1,
    list_files: Boolean = false,
    check_keywords: Set[String] = Set.empty,
    no_build: Boolean = false,
    system_mode: Boolean = false,
    verbose: Boolean = false,
    exclude_sessions: List[String] = Nil,
    sessions: List[String] = Nil): Build_Results =
  {
    /* session tree and dependencies */

    val full_tree = Sessions.load(options.int("completion_limit") = 0, dirs, select_dirs)
    val (selected, selected_tree) =
      full_tree.selection(requirements, all_sessions,
        exclude_session_groups, exclude_sessions, session_groups, sessions)

    val deps = dependencies(progress, true, verbose, list_files, check_keywords, selected_tree)

    def session_sources_stamp(name: String): String =
      sources_stamp(selected_tree(name).meta_digest :: deps.sources(name))

    val store = Sessions.store(system_mode)


    /* queue with scheduling information */

    def load_timings(name: String): (List[Properties.T], Double) =
    {
      val (path, text) =
        store.find_log_gz(name) match {
          case Some(path) => (path, File.read_gzip(path))
          case None =>
            store.find_log(name) match {
              case Some(path) => (path, File.read(path))
              case None => (Path.current, "")
            }
        }

      def ignore_error(msg: String): (List[Properties.T], Double) =
      {
        Output.warning("Ignoring bad log file: " + path + (if (msg == "") "" else "\n" + msg))
        (Nil, 0.0)
      }

      try {
        val info = parse_log(false, text)
        val session_timing = Markup.Elapsed.unapply(info.session_timing) getOrElse 0.0
        (info.command_timings, session_timing)
      }
      catch {
        case ERROR(msg) => ignore_error(msg)
        case exn: java.lang.Error => ignore_error(Exn.message(exn))
        case _: XML.Error => ignore_error("")
      }
    }

    val queue = Queue(selected_tree, load_timings)


    /* main build process */

    store.prepare_output()

    // optional cleanup
    if (clean_build) {
      for (name <- full_tree.graph.all_succs(selected)) {
        val files =
          List(Path.basic(name), Sessions.log(name), Sessions.log_gz(name)).
            map(store.output_dir + _).filter(_.is_file)
        if (files.nonEmpty) progress.echo("Cleaning " + name + " ...")
        if (!files.forall(p => p.file.delete)) progress.echo(name + " FAILED to delete")
      }
    }

    // scheduler loop
    case class Result(current: Boolean, heap_stamp: Option[String], process: Option[Process_Result])
    {
      def ok: Boolean =
        process match {
          case None => false
          case Some(res) => res.rc == 0
        }
    }

    def sleep()
    {
      try { Thread.sleep(500) }
      catch { case Exn.Interrupt() => Exn.Interrupt.impose() }
    }

    @tailrec def loop(
      pending: Queue,
      running: Map[String, (List[String], Job)],
      results: Map[String, Result]): Map[String, Result] =
    {
      if (pending.is_empty) results
      else {
        if (progress.stopped)
          for ((_, (_, job)) <- running) job.terminate

        running.find({ case (_, (_, job)) => job.is_finished }) match {
          case Some((name, (input_heaps, job))) =>
            //{{{ finish job

            val process_result = job.join
            process_result.err_lines.foreach(progress.echo(_))
            if (process_result.ok)
              progress.echo("Finished " + name + " (" + process_result.timing.message_resources + ")")

            val process_result_tail =
            {
              val lines = process_result.out_lines.filterNot(_.startsWith("\f"))
              val tail = job.info.options.int("process_output_tail")
              val lines1 = if (tail == 0) lines else lines.drop(lines.length - tail max 0)
              process_result.copy(
                out_lines =
                  "(see also " + (store.output_dir + Sessions.log(name)).file.toString + ")" ::
                  lines1)
            }

            val heap_stamp =
              if (process_result.ok) {
                (store.output_dir + Sessions.log(name)).file.delete
                val heap_stamp =
                  for (path <- job.output_path; stamp <- File.time_stamp(path))
                    yield stamp

                File.write_gzip(store.output_dir + Sessions.log_gz(name),
                  Library.terminate_lines(
                    session_sources_stamp(name) ::
                    input_heaps.map(INPUT_HEAP + _) :::
                    heap_stamp.toList.map(OUTPUT_HEAP + _) :::
                    List(LOG_START) ::: process_result.out_lines))

                heap_stamp
              }
              else {
                (store.output_dir + Path.basic(name)).file.delete
                (store.output_dir + Sessions.log_gz(name)).file.delete

                File.write(store.output_dir + Sessions.log(name),
                  Library.terminate_lines(process_result.out_lines))
                progress.echo(name + " FAILED")
                if (!process_result.interrupted) progress.echo(process_result_tail.out)

                None
              }
            loop(pending - name, running - name,
              results + (name -> Result(false, heap_stamp, Some(process_result_tail))))
            //}}}
          case None if running.size < (max_jobs max 1) =>
            //{{{ check/start next job
            pending.dequeue(running.isDefinedAt(_)) match {
              case Some((name, info)) =>
                val ancestor_results = selected_tree.ancestors(name).map(results(_))
                val ancestor_heaps = ancestor_results.flatMap(_.heap_stamp)

                val do_output = build_heap || Sessions.is_pure(name) || queue.is_inner(name)

                val (current, heap_stamp) =
                {
                  store.find(name) match {
                    case Some((log_gz, heap_stamp)) =>
                      read_stamps(log_gz) match {
                        case Some((sources, input_heaps, output_heaps)) =>
                          val current =
                            sources == session_sources_stamp(name) &&
                            input_heaps == ancestor_heaps.map(INPUT_HEAP + _) &&
                            output_heaps == heap_stamp.toList.map(OUTPUT_HEAP + _) &&
                            !(do_output && heap_stamp.isEmpty)
                          (current, heap_stamp)
                        case None => (false, None)
                      }
                    case None => (false, None)
                  }
                }
                val all_current = current && ancestor_results.forall(_.current)

                if (all_current)
                  loop(pending - name, running,
                    results + (name -> Result(true, heap_stamp, Some(Process_Result(0)))))
                else if (no_build) {
                  if (verbose) progress.echo("Skipping " + name + " ...")
                  loop(pending - name, running,
                    results + (name -> Result(false, heap_stamp, Some(Process_Result(1)))))
                }
                else if (ancestor_results.forall(_.ok) && !progress.stopped) {
                  progress.echo((if (do_output) "Building " else "Running ") + name + " ...")
                  val job =
                    new Job(progress, name, info, selected_tree, store, do_output, verbose,
                      deps(name).session_graph, queue.command_timings(name))
                  loop(pending, running + (name -> (ancestor_heaps, job)), results)
                }
                else {
                  progress.echo(name + " CANCELLED")
                  loop(pending - name, running, results + (name -> Result(false, heap_stamp, None)))
                }
              case None => sleep(); loop(pending, running, results)
            }
            ///}}}
          case None => sleep(); loop(pending, running, results)
        }
      }
    }


    /* build results */

    val results =
      if (deps.is_empty) {
        progress.echo(Output.warning_text("Nothing to build"))
        Map.empty[String, Result]
      }
      else loop(queue, Map.empty, Map.empty)


    /* global browser info */

    if (!no_build) {
      val browser_chapters =
        (for {
          (name, result) <- results.iterator
          if result.ok && !Sessions.is_pure(name)
          info = full_tree(name)
          if info.options.bool("browser_info")
        } yield (info.chapter, (name, info.description))).toList.groupBy(_._1).
            map({ case (chapter, es) => (chapter, es.map(_._2)) }).filterNot(_._2.isEmpty)

      for ((chapter, entries) <- browser_chapters)
        Present.update_chapter_index(store.browser_info, chapter, entries)

      if (browser_chapters.nonEmpty) Present.make_global_index(store.browser_info)
    }

    new Build_Results((for ((name, result) <- results.iterator) yield (name, result.process)).toMap)
  }



  /** build **/

  def build(
    options: Options,
    progress: Progress = Ignore_Progress,
    requirements: Boolean = false,
    all_sessions: Boolean = false,
    build_heap: Boolean = false,
    clean_build: Boolean = false,
    dirs: List[Path] = Nil,
    select_dirs: List[Path] = Nil,
    exclude_session_groups: List[String] = Nil,
    session_groups: List[String] = Nil,
    max_jobs: Int = 1,
    list_files: Boolean = false,
    check_keywords: Set[String] = Set.empty,
    no_build: Boolean = false,
    system_mode: Boolean = false,
    verbose: Boolean = false,
    exclude_sessions: List[String] = Nil,
    sessions: List[String] = Nil): Int =
  {
    val results =
      build_results(options, progress, requirements, all_sessions, build_heap, clean_build,
        dirs, select_dirs, exclude_session_groups, session_groups, max_jobs, list_files,
        check_keywords, no_build, system_mode, verbose, exclude_sessions, sessions)

    if (results.rc != 0 && (verbose || !no_build)) {
      val unfinished =
        (for {
          name <- results.sessions.iterator
          if !results(name).ok
         } yield name).toList.sorted
      progress.echo("Unfinished session(s): " + commas(unfinished))
    }

    results.rc
  }


  /* command line entry point */

  def main(args: Array[String])
  {
    Command_Line.tool {
      def show_settings(): String =
        cat_lines(List(
          "ISABELLE_BUILD_OPTIONS=" +
            quote(Isabelle_System.getenv("ISABELLE_BUILD_OPTIONS")),
          "ISABELLE_BUILD_JAVA_OPTIONS=" +
            quote(Isabelle_System.getenv("ISABELLE_BUILD_JAVA_OPTIONS")),
          "",
          "ML_PLATFORM=" + quote(Isabelle_System.getenv("ML_PLATFORM")),
          "ML_HOME=" + quote(Isabelle_System.getenv("ML_HOME")),
          "ML_SYSTEM=" + quote(Isabelle_System.getenv("ML_SYSTEM")),
          "ML_OPTIONS=" + quote(Isabelle_System.getenv("ML_OPTIONS"))))

      val build_options = Word.explode(Isabelle_System.getenv("ISABELLE_BUILD_OPTIONS"))

      var select_dirs: List[Path] = Nil
      var requirements = false
      var exclude_session_groups: List[String] = Nil
      var all_sessions = false
      var build_heap = false
      var clean_build = false
      var dirs: List[Path] = Nil
      var session_groups: List[String] = Nil
      var max_jobs = 1
      var check_keywords: Set[String] = Set.empty
      var list_files = false
      var no_build = false
      var options = (Options.init() /: build_options)(_ + _)
      var system_mode = false
      var verbose = false
      var exclude_sessions: List[String] = Nil

      val getopts = Getopts("""
Usage: isabelle build [OPTIONS] [SESSIONS ...]

  Options are:
    -D DIR       include session directory and select its sessions
    -R           operate on requirements of selected sessions
    -X NAME      exclude sessions from group NAME and all descendants
    -a           select all sessions
    -b           build heap images
    -c           clean build
    -d DIR       include session directory
    -g NAME      select session group NAME
    -j INT       maximum number of parallel jobs (default 1)
    -k KEYWORD   check theory sources for conflicts with proposed keywords
    -l           list session source files
    -n           no build -- test dependencies only
    -o OPTION    override Isabelle system OPTION (via NAME=VAL or NAME)
    -s           system build mode: produce output in ISABELLE_HOME
    -v           verbose
    -x NAME      exclude session NAME and all descendants

  Build and manage Isabelle sessions, depending on implicit settings:

""" + Library.prefix_lines("  ", show_settings()),
        "D:" -> (arg => select_dirs = select_dirs ::: List(Path.explode(arg))),
        "R" -> (_ => requirements = true),
        "X:" -> (arg => exclude_session_groups = exclude_session_groups ::: List(arg)),
        "a" -> (_ => all_sessions = true),
        "b" -> (_ => build_heap = true),
        "c" -> (_ => clean_build = true),
        "d:" -> (arg => dirs = dirs ::: List(Path.explode(arg))),
        "g:" -> (arg => session_groups = session_groups ::: List(arg)),
        "j:" -> (arg => max_jobs = Properties.Value.Int.parse(arg)),
        "k:" -> (arg => check_keywords = check_keywords + arg),
        "l" -> (_ => list_files = true),
        "n" -> (_ => no_build = true),
        "o:" -> (arg => options = options + arg),
        "s" -> (_ => system_mode = true),
        "v" -> (_ => verbose = true),
        "x:" -> (arg => exclude_sessions = exclude_sessions ::: List(arg)))

      val sessions = getopts(args)

      val progress = new Console_Progress(verbose)

      if (verbose) {
        progress.echo(
          Library.trim_line(
            Isabelle_System.bash(
              """echo "Started at $(date) ($ML_IDENTIFIER on $(hostname))" """).out) + "\n")
        progress.echo(show_settings() + "\n")
      }

      val start_time = Time.now()
      val results =
        progress.interrupt_handler {
          build_results(options, progress, requirements, all_sessions, build_heap, clean_build,
            dirs, select_dirs, exclude_session_groups, session_groups, max_jobs, list_files,
            check_keywords, no_build, system_mode, verbose, exclude_sessions, sessions)
        }
      val elapsed_time = Time.now() - start_time

      if (verbose) {
        progress.echo("\n" +
          Library.trim_line(
            Isabelle_System.bash("""echo -n "Finished at "; date""").out))
      }

      val total_timing =
        (Timing.zero /: results.sessions.iterator.map(a => results(a).timing))(_ + _).
          copy(elapsed = elapsed_time)
      progress.echo(total_timing.message_resources)

      results.rc
    }
  }


  /* PIDE protocol */

  def build_theories(
    session: Session, master_dir: Path, theories: List[(Options, List[Path])]): Promise[XML.Body] =
      session.get_protocol_handler(classOf[Handler].getName) match {
        case Some(handler: Handler) => handler.build_theories(session, master_dir, theories)
        case _ => error("Cannot invoke build_theories: bad protocol handler")
      }

  class Handler(progress: Progress, session_name: String) extends Session.Protocol_Handler
  {
    private val pending = Synchronized(Map.empty[String, Promise[XML.Body]])

    def build_theories(
      session: Session, master_dir: Path, theories: List[(Options, List[Path])]): Promise[XML.Body] =
    {
      val promise = Future.promise[XML.Body]
      val id = Document_ID.make().toString
      pending.change(promises => promises + (id -> promise))
      session.build_theories(id, master_dir, theories)
      promise
    }

    private def loading_theory(prover: Prover, msg: Prover.Protocol_Output): Boolean =
      msg.properties match {
        case Markup.Loading_Theory(name) => progress.theory(session_name, name); true
        case _ => false
      }

    private def build_theories_result(prover: Prover, msg: Prover.Protocol_Output): Boolean =
      msg.properties match {
        case Markup.Build_Theories_Result(id) =>
          pending.change_result(promises =>
            promises.get(id) match {
              case Some(promise) =>
                val error_message =
                  try { YXML.parse_body(Symbol.decode(msg.text)) }
                  catch { case exn: Throwable => List(XML.Text(Exn.message(exn))) }
                promise.fulfill(error_message)
                (true, promises - id)
              case None =>
                (false, promises)
            })
        case _ => false
      }

    override def stop(prover: Prover): Unit =
      pending.change(promises => { for ((_, promise) <- promises) promise.cancel; Map.empty })

    val functions =
      Map(
        Markup.BUILD_THEORIES_RESULT -> build_theories_result _,
        Markup.LOADING_THEORY -> loading_theory _)
  }
}
