/*  Title:      Pure/Tools/dump.scala
    Author:     Makarius

Dump cumulative PIDE session database.
*/

package isabelle


object Dump
{
  /* aspects */

  sealed case class Aspect_Args(
    options: Options,
    progress: Progress,
    deps: Sessions.Deps,
    output_dir: Path,
    snapshot: Document.Snapshot,
    node_status: Document_Status.Node_Status)
  {
    def write(file_name: Path, bytes: Bytes)
    {
      val path = output_dir + Path.basic(snapshot.node_name.theory) + file_name
      Isabelle_System.mkdirs(path.dir)
      Bytes.write(path, bytes)
    }

    def write(file_name: Path, text: String): Unit =
      write(file_name, Bytes(text))

    def write(file_name: Path, body: XML.Body): Unit =
      write(file_name, Symbol.encode(YXML.string_of_body(body)))
  }

  sealed case class Aspect(name: String, description: String, operation: Aspect_Args => Unit,
    options: List[String] = Nil)
  {
    override def toString: String = name
  }

  val known_aspects: List[Aspect] =
    List(
      Aspect("markup", "PIDE markup (YXML format)",
        { case args =>
            args.write(Path.explode("markup.yxml"),
              args.snapshot.markup_to_XML(Text.Range.full, Markup.Elements.full))
        }),
      Aspect("messages", "output messages (YXML format)",
        { case args =>
            args.write(Path.explode("messages.yxml"),
              args.snapshot.messages.iterator.map(_._1).toList)
        }),
      Aspect("latex", "generated LaTeX source",
        { case args =>
            for (entry <- args.snapshot.exports if entry.name == "document.tex")
              args.write(Path.explode(entry.name), entry.uncompressed())
        }, options = List("editor_presentation", "export_document")),
      Aspect("theory", "foundational theory content",
        { case args =>
            for {
              entry <- args.snapshot.exports
              if entry.name.startsWith(Export_Theory.export_prefix)
            } args.write(Path.explode(entry.name), entry.uncompressed())
        }, options = List("editor_presentation", "export_theory"))
    ).sortBy(_.name)

  def show_aspects: String =
    cat_lines(known_aspects.map(aspect => aspect.name + " - " + aspect.description))

  def the_aspect(name: String): Aspect =
    known_aspects.find(aspect => aspect.name == name) getOrElse
      error("Unknown aspect " + quote(name))


  /* session */

  def session(dump_options: Options, logic: String,
    consume: (Sessions.Deps, Document.Snapshot, Document_Status.Node_Status) => Unit,
    progress: Progress = No_Progress,
    log: Logger = No_Logger,
    dirs: List[Path] = Nil,
    select_dirs: List[Path] = Nil,
    system_mode: Boolean = false,
    selection: Sessions.Selection = Sessions.Selection.empty): Boolean =
  {
    /* dependencies */

    val deps =
      Sessions.load_structure(dump_options, dirs = dirs, select_dirs = select_dirs).
        selection_deps(dump_options, selection, uniform_session = true, loading_sessions = true)

    val include_sessions =
      deps.sessions_structure.imports_topological_order

    val use_theories =
      for { (_, name) <- deps.used_theories_condition(dump_options, progress.echo_warning) }
      yield name.theory


    /* dump aspects asynchronously */

    object Consumer
    {
      private val consumer_ok = Synchronized(true)

      private val consumer =
        Consumer_Thread.fork(name = "dump")(
          consume = (args: (Document.Snapshot, Document_Status.Node_Status)) =>
            {
              val (snapshot, node_status) = args
              if (node_status.ok) consume(deps, snapshot, node_status)
              else {
                consumer_ok.change(_ => false)
                for ((tree, pos) <- snapshot.messages if Protocol.is_error(tree)) {
                  val msg = XML.content(Pretty.formatted(List(tree)))
                  progress.echo_error_message("Error" + Position.here(pos) + ":\n" + msg)
                }
              }
              true
            })

      def apply(snapshot: Document.Snapshot, node_status: Document_Status.Node_Status): Unit =
        consumer.send((snapshot, node_status))

      def shutdown(): Boolean =
      {
        consumer.shutdown()
        consumer_ok.value
      }
    }


    /* run session */

    val session =
      Headless.start_session(dump_options, logic, session_dirs = dirs ::: select_dirs,
        include_sessions = include_sessions, progress = progress, log = log)

    val use_theories_result =
      session.use_theories(use_theories, progress = progress, commit = Some(Consumer.apply _))

    session.stop()

    val consumer_ok = Consumer.shutdown()

    use_theories_result.nodes_pending match {
      case Nil =>
      case pending => error("Pending theories " + commas_quote(pending.map(p => p._1.toString)))
    }

    use_theories_result.ok && consumer_ok
  }


  /* dump */

  val default_output_dir: Path = Path.explode("dump")

  def make_options(options: Options, aspects: List[Aspect] = Nil): Options =
  {
    val options0 = if (NUMA.enabled) NUMA.policy_options(options) else options
    val options1 =
      options0 + "completion_limit=0" + "ML_statistics=false" +
        "parallel_proofs=0" + "editor_tracing_messages=0"
    (options1 /: aspects)({ case (opts, aspect) => (opts /: aspect.options)(_ + _) })
  }

  def dump(options: Options, logic: String,
    aspects: List[Aspect] = Nil,
    progress: Progress = No_Progress,
    log: Logger = No_Logger,
    dirs: List[Path] = Nil,
    select_dirs: List[Path] = Nil,
    output_dir: Path = default_output_dir,
    system_mode: Boolean = false,
    selection: Sessions.Selection = Sessions.Selection.empty): Boolean =
  {
    if (Build.build_logic(options, logic, build_heap = true, progress = progress,
      dirs = dirs ::: select_dirs, system_mode = system_mode) != 0) error(logic + " FAILED")

    val dump_options = make_options(options, aspects)

    def consume(
      deps: Sessions.Deps,
      snapshot: Document.Snapshot,
      node_status: Document_Status.Node_Status)
    {
      val aspect_args = Aspect_Args(dump_options, progress, deps, output_dir, snapshot, node_status)
      aspects.foreach(_.operation(aspect_args))
    }

    session(dump_options, logic, consume _,
      progress = progress, log = log, dirs = dirs, select_dirs = select_dirs, selection = selection)
  }


  /* Isabelle tool wrapper */

  val isabelle_tool =
    Isabelle_Tool("dump", "dump cumulative PIDE session database", args =>
    {
      var aspects: List[Aspect] = known_aspects
      var base_sessions: List[String] = Nil
      var select_dirs: List[Path] = Nil
      var output_dir = default_output_dir
      var requirements = false
      var exclude_session_groups: List[String] = Nil
      var all_sessions = false
      var dirs: List[Path] = Nil
      var session_groups: List[String] = Nil
      var logic = Isabelle_System.getenv("ISABELLE_LOGIC")
      var options = Options.init()
      var system_mode = false
      var verbose = false
      var exclude_sessions: List[String] = Nil

      val getopts = Getopts("""
Usage: isabelle dump [OPTIONS] [SESSIONS ...]

  Options are:
    -A NAMES     dump named aspects (default: """ + known_aspects.mkString("\"", ",", "\"") + """)
    -B NAME      include session NAME and all descendants
    -D DIR       include session directory and select its sessions
    -O DIR       output directory for dumped files (default: """ + default_output_dir + """)
    -R           operate on requirements of selected sessions
    -X NAME      exclude sessions from group NAME and all descendants
    -a           select all sessions
    -d DIR       include session directory
    -g NAME      select session group NAME
    -l NAME      logic session name (default ISABELLE_LOGIC=""" + quote(logic) + """)
    -o OPTION    override Isabelle system OPTION (via NAME=VAL or NAME)
    -s           system build mode for logic image
    -v           verbose
    -x NAME      exclude session NAME and all descendants

  Dump cumulative PIDE session database, with the following aspects:

""" + Library.prefix_lines("    ", show_aspects) + "\n",
      "A:" -> (arg => aspects = Library.distinct(space_explode(',', arg)).map(the_aspect(_))),
      "B:" -> (arg => base_sessions = base_sessions ::: List(arg)),
      "D:" -> (arg => select_dirs = select_dirs ::: List(Path.explode(arg))),
      "O:" -> (arg => output_dir = Path.explode(arg)),
      "R" -> (_ => requirements = true),
      "X:" -> (arg => exclude_session_groups = exclude_session_groups ::: List(arg)),
      "a" -> (_ => all_sessions = true),
      "d:" -> (arg => dirs = dirs ::: List(Path.explode(arg))),
      "g:" -> (arg => session_groups = session_groups ::: List(arg)),
      "l:" -> (arg => logic = arg),
      "o:" -> (arg => options = options + arg),
      "s" -> (_ => system_mode = true),
      "v" -> (_ => verbose = true),
      "x:" -> (arg => exclude_sessions = exclude_sessions ::: List(arg)))

      val sessions = getopts(args)

      val progress = new Console_Progress(verbose = verbose)

      val ok =
        progress.interrupt_handler {
          dump(options, logic,
            aspects = aspects,
            progress = progress,
            dirs = dirs,
            select_dirs = select_dirs,
            output_dir = output_dir,
            selection = Sessions.Selection(
              requirements = requirements,
              all_sessions = all_sessions,
              base_sessions = base_sessions,
              exclude_session_groups = exclude_session_groups,
              exclude_sessions = exclude_sessions,
              session_groups = session_groups,
              sessions = sessions))
        }

      if (!ok) sys.exit(2)
    })
}
