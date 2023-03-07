/*  Title:      Pure/Tools/build.scala
    Author:     Makarius
    Options:    :folding=explicit:

Command-line tools to build and manage Isabelle sessions.
*/

package isabelle

import scala.collection.mutable
import scala.util.matching.Regex


object Build {
  /** "isabelle build" **/

  /* results */

  object Results {
    def apply(context: Build_Process.Context, results: Map[String, Process_Result]): Results =
      new Results(context.store, context.build_deps, results)
  }

  class Results private(
    val store: Sessions.Store,
    val deps: Sessions.Deps,
    results: Map[String, Process_Result]
  ) {
    def cache: Term.Cache = store.cache

    def sessions_ok: List[String] =
      (for {
        name <- deps.sessions_structure.build_topological_order.iterator
        result <- results.get(name) if result.ok
      } yield name).toList

    def info(name: String): Sessions.Info = deps.sessions_structure(name)
    def sessions: Set[String] = results.keySet
    def cancelled(name: String): Boolean = !results(name).defined
    def apply(name: String): Process_Result = results(name).strict
    val rc: Int = results.valuesIterator.map(_.strict.rc).foldLeft(Process_Result.RC.ok)(_ max _)
    def ok: Boolean = rc == Process_Result.RC.ok

    def unfinished: List[String] = sessions.iterator.filterNot(apply(_).ok).toList.sorted

    override def toString: String = rc.toString
  }


  /* engine */

  class Engine(val name: String) extends Isabelle_System.Service {
    override def toString: String = name
    def init(build_context: Build_Process.Context, build_progress: Progress): Build_Process =
      new Build_Process(build_context, build_progress)
  }

  class Default_Engine extends Engine("") { override def toString: String = "<default>" }

  lazy val engines: List[Engine] =
    Isabelle_System.make_services(classOf[Engine])

  def get_engine(name: String): Engine =
    engines.find(_.name == name).getOrElse(error("Bad build engine " + quote(name)))


  /* build */

  def build(
    options: Options,
    selection: Sessions.Selection = Sessions.Selection.empty,
    browser_info: Browser_Info.Config = Browser_Info.Config.none,
    progress: Progress = new Progress,
    check_unknown_files: Boolean = false,
    build_heap: Boolean = false,
    clean_build: Boolean = false,
    dirs: List[Path] = Nil,
    select_dirs: List[Path] = Nil,
    infos: List[Sessions.Info] = Nil,
    numa_shuffling: Boolean = false,
    max_jobs: Int = 1,
    list_files: Boolean = false,
    check_keywords: Set[String] = Set.empty,
    fresh_build: Boolean = false,
    no_build: Boolean = false,
    soft_build: Boolean = false,
    export_files: Boolean = false,
    augment_options: String => List[Options.Spec] = _ => Nil,
    session_setup: (String, Session) => Unit = (_, _) => ()
  ): Results = {
    val build_options =
      options +
        "completion_limit=0" +
        "editor_tracing_messages=0" +
        ("pide_reports=" + options.bool("build_pide_reports"))

    val store = Sessions.store(build_options)

    Isabelle_Fonts.init()


    /* session selection and dependencies */

    val full_sessions =
      Sessions.load_structure(build_options, dirs = dirs, select_dirs = select_dirs, infos = infos,
        augment_options = augment_options)
    val full_sessions_selection = full_sessions.imports_selection(selection)

    val build_deps = {
      val deps0 =
        Sessions.deps(full_sessions.selection(selection), progress = progress, inlined_files = true,
          list_files = list_files, check_keywords = check_keywords).check_errors

      if (soft_build && !fresh_build) {
        val outdated =
          deps0.sessions_structure.build_topological_order.flatMap(name =>
            store.try_open_database(name) match {
              case Some(db) =>
                using(db)(store.read_build(_, name)) match {
                  case Some(build)
                  if build.ok && build.sources == deps0.sources_shasum(name) => None
                  case _ => Some(name)
                }
              case None => Some(name)
            })

        Sessions.deps(full_sessions.selection(Sessions.Selection(sessions = outdated)),
          progress = progress, inlined_files = true).check_errors
      }
      else deps0
    }


    /* check unknown files */

    if (check_unknown_files) {
      val source_files =
        (for {
          (_, base) <- build_deps.session_bases.iterator
          (path, _) <- base.session_sources.iterator
        } yield path).toList
      Mercurial.check_files(source_files)._2 match {
        case Nil =>
        case unknown_files =>
          progress.echo_warning("Unknown files (not part of the underlying Mercurial repository):" +
            unknown_files.map(File.standard_path).sorted.mkString("\n  ", "\n  ", ""))
      }
    }


    /* build process and results */

    val build_context =
      Build_Process.Context(store, build_deps, progress = progress,
        hostname = Isabelle_System.hostname(build_options.string("build_hostname")),
        build_heap = build_heap, numa_shuffling = numa_shuffling, max_jobs = max_jobs,
        fresh_build = fresh_build, no_build = no_build, session_setup = session_setup)

    store.prepare_output()
    build_context.prepare_database()

    if (clean_build) {
      for (name <- full_sessions.imports_descendants(full_sessions_selection)) {
        val (relevant, ok) = store.clean_output(name)
        if (relevant) {
          if (ok) progress.echo("Cleaned " + name)
          else progress.echo(name + " FAILED to clean")
        }
      }
    }

    val results =
      Isabelle_Thread.uninterruptible {
        val engine = get_engine(build_options.string("build_engine"))
        using(engine.init(build_context, progress)) { build_process =>
          val res = build_process.run(master = true)
          Results(build_context, res)
        }
      }

    if (export_files) {
      for (name <- full_sessions_selection.iterator if results(name).ok) {
        val info = results.info(name)
        if (info.export_files.nonEmpty) {
          progress.echo("Exporting " + info.name + " ...")
          for ((dir, prune, pats) <- info.export_files) {
            Export.export_files(store, name, info.dir + dir,
              progress = if (progress.verbose) progress else new Progress,
              export_prune = prune,
              export_patterns = pats)
          }
        }
      }
    }

    val presentation_sessions =
      results.sessions_ok.filter(name => browser_info.enabled(results.info(name)))
    if (presentation_sessions.nonEmpty && !progress.stopped) {
      Browser_Info.build(browser_info, results.store, results.deps, presentation_sessions,
        progress = progress)
    }

    if (!results.ok && (progress.verbose || !no_build)) {
      progress.echo("Unfinished session(s): " + commas(results.unfinished))
    }

    results
  }


  /* build logic image */

  def build_logic(options: Options, logic: String,
    progress: Progress = new Progress,
    build_heap: Boolean = false,
    dirs: List[Path] = Nil,
    fresh: Boolean = false,
    strict: Boolean = false
  ): Int = {
    val selection = Sessions.Selection.session(logic)
    val rc =
      if (!fresh && build(options, selection = selection,
            build_heap = build_heap, no_build = true, dirs = dirs).ok) Process_Result.RC.ok
      else {
        progress.echo("Build started for Isabelle/" + logic + " ...")
        build(options, selection = selection, progress = progress,
          build_heap = build_heap, fresh_build = fresh, dirs = dirs).rc
      }
    if (strict && rc != Process_Result.RC.ok) error("Failed to build Isabelle/" + logic) else rc
  }


  /* command-line wrapper */

  val isabelle_tool1 = Isabelle_Tool("build", "build and manage Isabelle sessions",
    Scala_Project.here,
    { args =>
      val build_options = Word.explode(Isabelle_System.getenv("ISABELLE_BUILD_OPTIONS"))

      var base_sessions: List[String] = Nil
      var select_dirs: List[Path] = Nil
      var numa_shuffling = false
      var browser_info = Browser_Info.Config.none
      var requirements = false
      var soft_build = false
      var exclude_session_groups: List[String] = Nil
      var all_sessions = false
      var build_heap = false
      var clean_build = false
      var dirs: List[Path] = Nil
      var export_files = false
      var fresh_build = false
      var session_groups: List[String] = Nil
      var max_jobs = 1
      var check_keywords: Set[String] = Set.empty
      var list_files = false
      var no_build = false
      var options = Options.init(opts = build_options)
      var verbose = false
      var exclude_sessions: List[String] = Nil

      val getopts = Getopts("""
Usage: isabelle build [OPTIONS] [SESSIONS ...]

  Options are:
    -B NAME      include session NAME and all descendants
    -D DIR       include session directory and select its sessions
    -N           cyclic shuffling of NUMA CPU nodes (performance tuning)
    -P DIR       enable HTML/PDF presentation in directory (":" for default)
    -R           refer to requirements of selected sessions
    -S           soft build: only observe changes of sources, not heap images
    -X NAME      exclude sessions from group NAME and all descendants
    -a           select all sessions
    -b           build heap images
    -c           clean build
    -d DIR       include session directory
    -e           export files from session specification into file-system
    -f           fresh build
    -g NAME      select session group NAME
    -j INT       maximum number of parallel jobs (default 1)
    -k KEYWORD   check theory sources for conflicts with proposed keywords
    -l           list session source files
    -n           no build -- take existing session build databases
    -o OPTION    override Isabelle system OPTION (via NAME=VAL or NAME)
    -v           verbose
    -x NAME      exclude session NAME and all descendants

  Build and manage Isabelle sessions, depending on implicit settings:

""" + Library.indent_lines(2,  Build_Log.Settings.show()) + "\n",
        "B:" -> (arg => base_sessions = base_sessions ::: List(arg)),
        "D:" -> (arg => select_dirs = select_dirs ::: List(Path.explode(arg))),
        "N" -> (_ => numa_shuffling = true),
        "P:" -> (arg => browser_info = Browser_Info.Config.make(arg)),
        "R" -> (_ => requirements = true),
        "S" -> (_ => soft_build = true),
        "X:" -> (arg => exclude_session_groups = exclude_session_groups ::: List(arg)),
        "a" -> (_ => all_sessions = true),
        "b" -> (_ => build_heap = true),
        "c" -> (_ => clean_build = true),
        "d:" -> (arg => dirs = dirs ::: List(Path.explode(arg))),
        "e" -> (_ => export_files = true),
        "f" -> (_ => fresh_build = true),
        "g:" -> (arg => session_groups = session_groups ::: List(arg)),
        "j:" -> (arg => max_jobs = Value.Int.parse(arg)),
        "k:" -> (arg => check_keywords = check_keywords + arg),
        "l" -> (_ => list_files = true),
        "n" -> (_ => no_build = true),
        "o:" -> (arg => options = options + arg),
        "v" -> (_ => verbose = true),
        "x:" -> (arg => exclude_sessions = exclude_sessions ::: List(arg)))

      val sessions = getopts(args)

      val progress = new Console_Progress(verbose = verbose)

      val start_date = Date.now()

      val hostname = Isabelle_System.hostname(options.string("build_hostname"))
      progress.echo(
        "Started at " + Build_Log.print_date(start_date) +
          " (" + Isabelle_System.getenv("ML_IDENTIFIER") + " on " + hostname +")",
        verbose = true)
      progress.echo(Build_Log.Settings.show() + "\n", verbose = true)

      val results =
        progress.interrupt_handler {
          build(options,
            selection = Sessions.Selection(
              requirements = requirements,
              all_sessions = all_sessions,
              base_sessions = base_sessions,
              exclude_session_groups = exclude_session_groups,
              exclude_sessions = exclude_sessions,
              session_groups = session_groups,
              sessions = sessions),
            browser_info = browser_info,
            progress = progress,
            check_unknown_files = Mercurial.is_repository(Path.ISABELLE_HOME),
            build_heap = build_heap,
            clean_build = clean_build,
            dirs = dirs,
            select_dirs = select_dirs,
            numa_shuffling = Host.numa_check(progress, numa_shuffling),
            max_jobs = max_jobs,
            list_files = list_files,
            check_keywords = check_keywords,
            fresh_build = fresh_build,
            no_build = no_build,
            soft_build = soft_build,
            export_files = export_files)
        }
      val stop_date = Date.now()
      val elapsed_time = stop_date.time - start_date.time

      progress.echo("\nFinished at " + Build_Log.print_date(stop_date), verbose = true)

      val total_timing =
        results.sessions.iterator.map(a => results(a).timing).foldLeft(Timing.zero)(_ + _).
          copy(elapsed = elapsed_time)
      progress.echo(total_timing.message_resources)

      sys.exit(results.rc)
    })



  /** "isabelle log" **/

  /* theory markup/messages from session database */

  def read_theory(
    theory_context: Export.Theory_Context,
    unicode_symbols: Boolean = false
  ): Option[Document.Snapshot] = {
    def decode_bytes(bytes: Bytes): String =
      Symbol.output(unicode_symbols, UTF8.decode_permissive(bytes))

    def read(name: String): Export.Entry = theory_context(name, permissive = true)

    def read_xml(name: String): XML.Body =
      YXML.parse_body(decode_bytes(read(name).bytes), cache = theory_context.cache)

    def read_source_file(name: String): Sessions.Source_File =
      theory_context.session_context.source_file(name)

    for {
      id <- theory_context.document_id()
      (thy_file, blobs_files) <- theory_context.files(permissive = true)
    }
    yield {
      val master_dir =
        Path.explode(Url.strip_base_name(thy_file).getOrElse(
          error("Cannot determine theory master directory: " + quote(thy_file))))

      val blobs =
        blobs_files.map { name =>
          val path = Path.explode(name)
          val src_path = File.relative_path(master_dir, path).getOrElse(path)

          val file = read_source_file(name)
          val bytes = file.bytes
          val text = decode_bytes(bytes)
          val chunk = Symbol.Text_Chunk(text)

          Command.Blob(Document.Node.Name(name), src_path, Some((file.digest, chunk))) ->
            Document.Blobs.Item(bytes, text, chunk, changed = false)
        }

      val thy_source = decode_bytes(read_source_file(thy_file).bytes)
      val thy_xml = read_xml(Export.MARKUP)
      val blobs_xml =
        for (i <- (1 to blobs.length).toList)
          yield read_xml(Export.MARKUP + i)

      val markups_index = Command.Markup_Index.make(blobs.map(_._1))
      val markups =
        Command.Markups.make(
          for ((index, xml) <- markups_index.zip(thy_xml :: blobs_xml))
          yield index -> Markup_Tree.from_XML(xml))

      val results =
        Command.Results.make(
          for (elem @ XML.Elem(Markup(_, Markup.Serial(i)), _) <- read_xml(Export.MESSAGES))
            yield i -> elem)

      val command =
        Command.unparsed(thy_source, theory = true, id = id,
          node_name = Document.Node.Name(thy_file, theory = theory_context.theory),
          blobs_info = Command.Blobs_Info.make(blobs),
          markups = markups, results = results)

      val doc_blobs = Document.Blobs.make(blobs)

      Document.State.init.snippet(command, doc_blobs)
    }
  }


  /* print messages */

  def print_log(
    options: Options,
    sessions: List[String],
    theories: List[String] = Nil,
    message_head: List[Regex] = Nil,
    message_body: List[Regex] = Nil,
    progress: Progress = new Progress,
    margin: Double = Pretty.default_margin,
    breakgain: Double = Pretty.default_breakgain,
    metric: Pretty.Metric = Symbol.Metric,
    unicode_symbols: Boolean = false
  ): Unit = {
    val store = Sessions.store(options)
    val session = new Session(options, Resources.bootstrap)

    def check(filter: List[Regex], make_string: => String): Boolean =
      filter.isEmpty || {
        val s = Output.clean_yxml(make_string)
        filter.forall(r => r.findFirstIn(Output.clean_yxml(s)).nonEmpty)
      }

    def print(session_name: String): Unit = {
      using(Export.open_session_context0(store, session_name)) { session_context =>
        val result =
          for {
            db <- session_context.session_db()
            theories = store.read_theories(db, session_name)
            errors = store.read_errors(db, session_name)
            info <- store.read_build(db, session_name)
          } yield (theories, errors, info.return_code)
        result match {
          case None => store.error_database(session_name)
          case Some((used_theories, errors, rc)) =>
            theories.filterNot(used_theories.toSet) match {
              case Nil =>
              case bad => error("Unknown theories " + commas_quote(bad))
            }
            val print_theories =
              if (theories.isEmpty) used_theories else used_theories.filter(theories.toSet)

            for (thy <- print_theories) {
              val thy_heading = "\nTheory " + quote(thy) + " (in " + session_name + ")" + ":"

              Build_Job.read_theory(session_context.theory(thy), unicode_symbols = unicode_symbols) match {
                case None => progress.echo(thy_heading + " MISSING")
                case Some(snapshot) =>
                  val rendering = new Rendering(snapshot, options, session)
                  val messages =
                    rendering.text_messages(Text.Range.full)
                      .filter(message => progress.verbose || Protocol.is_exported(message.info))
                  if (messages.nonEmpty) {
                    val line_document = Line.Document(snapshot.node.source)
                    val buffer = new mutable.ListBuffer[String]
                    for (Text.Info(range, elem) <- messages) {
                      val line = line_document.position(range.start).line1
                      val pos = Position.Line_File(line, snapshot.node_name.node)
                      def message_text: String =
                        Protocol.message_text(elem, heading = true, pos = pos,
                          margin = margin, breakgain = breakgain, metric = metric)
                      val ok =
                        check(message_head, Protocol.message_heading(elem, pos)) &&
                        check(message_body, XML.content(Pretty.unformatted(List(elem))))
                      if (ok) buffer += message_text
                    }
                    if (buffer.nonEmpty) {
                      progress.echo(thy_heading)
                      buffer.foreach(progress.echo(_))
                    }
                  }
              }
            }

            if (errors.nonEmpty) {
              val msg = Symbol.output(unicode_symbols, cat_lines(errors))
              progress.echo("\nBuild errors:\n" + Output.error_message_text(msg))
            }
            if (rc != Process_Result.RC.ok) {
              progress.echo("\n" + Process_Result.RC.print_long(rc))
            }
        }
      }
    }

    val errors = new mutable.ListBuffer[String]
    for (session_name <- sessions) {
      Exn.interruptible_capture(print(session_name)) match {
        case Exn.Res(_) =>
        case Exn.Exn(exn) => errors += Exn.message(exn)
      }
    }
    if (errors.nonEmpty) error(cat_lines(errors.toList))
  }


  /* command-line wrapper */

  val isabelle_tool2 = Isabelle_Tool("log", "print messages from session build database",
    Scala_Project.here,
    { args =>
      /* arguments */

      var message_head = List.empty[Regex]
      var message_body = List.empty[Regex]
      var unicode_symbols = false
      var theories: List[String] = Nil
      var margin = Pretty.default_margin
      var options = Options.init()
      var verbose = false

      val getopts = Getopts("""
Usage: isabelle log [OPTIONS] [SESSIONS ...]

  Options are:
    -H REGEX     filter messages by matching against head
    -M REGEX     filter messages by matching against body
    -T NAME      restrict to given theories (multiple options possible)
    -U           output Unicode symbols
    -m MARGIN    margin for pretty printing (default: """ + margin + """)
    -o OPTION    override Isabelle system OPTION (via NAME=VAL or NAME)
    -v           print all messages, including information etc.

  Print messages from the session build database of the given sessions,
  without any checks against current sources nor session structure: results
  from old sessions or failed builds can be printed as well.

  Multiple options -H and -M are conjunctive: all given patterns need to
  match. Patterns match any substring, but ^ or $ may be used to match the
  start or end explicitly.
""",
        "H:" -> (arg => message_head = message_head ::: List(arg.r)),
        "M:" -> (arg => message_body = message_body ::: List(arg.r)),
        "T:" -> (arg => theories = theories ::: List(arg)),
        "U" -> (_ => unicode_symbols = true),
        "m:" -> (arg => margin = Value.Double.parse(arg)),
        "o:" -> (arg => options = options + arg),
        "v" -> (_ => verbose = true))

      val sessions = getopts(args)

      val progress = new Console_Progress(verbose = verbose)

      if (sessions.isEmpty) progress.echo_warning("No sessions to print")
      else {
        print_log(options, sessions, theories = theories, message_head = message_head,
          message_body = message_body, margin = margin, progress = progress,
          unicode_symbols = unicode_symbols)
      }
    })
}
