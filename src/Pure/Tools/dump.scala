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
    deps: Sessions.Deps,
    progress: Progress,
    output_dir: Path,
    snapshot: Document.Snapshot,
    status: Document_Status.Node_Status)
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
        }, options = List("export_document")),
      Aspect("theory", "foundational theory content",
        { case args =>
            for {
              entry <- args.snapshot.exports
              if entry.name.startsWith(Export_Theory.export_prefix)
            } args.write(Path.explode(entry.name), entry.uncompressed())
        }, options = List("export_theory"))
    ).sortBy(_.name)

  def show_aspects: String =
    cat_lines(known_aspects.map(aspect => aspect.name + " - " + aspect.description))

  def the_aspect(name: String): Aspect =
    known_aspects.find(aspect => aspect.name == name) getOrElse
      error("Unknown aspect " + quote(name))


  /* context and session */

  sealed case class Args(
    session: Headless.Session,
    snapshot: Document.Snapshot,
    status: Document_Status.Node_Status)
  {
    def print_node: String = snapshot.node_name.toString
  }

  object Context
  {
    def apply(
      options: Options,
      aspects: List[Aspect] = Nil,
      progress: Progress = No_Progress,
      dirs: List[Path] = Nil,
      select_dirs: List[Path] = Nil,
      selection: Sessions.Selection = Sessions.Selection.empty): Context =
    {
      val session_options: Options =
      {
        val options0 = if (NUMA.enabled) NUMA.policy_options(options) else options
        val options1 =
          options0 +
            "completion_limit=0" +
            "ML_statistics=false" +
            "parallel_proofs=0" +
            "editor_tracing_messages=0" +
            "editor_presentation"
        (options1 /: aspects)({ case (opts, aspect) => (opts /: aspect.options)(_ + _) })
      }

      val deps: Sessions.Deps =
        Sessions.load_structure(session_options, dirs = dirs, select_dirs = select_dirs).
          selection_deps(session_options, selection, progress = progress,
            uniform_session = true, loading_sessions = true).check_errors

      new Context(options, progress, dirs, select_dirs, session_options, deps)
    }
  }

  class Context private(
    val options: Options,
    val progress: Progress,
    val dirs: List[Path],
    val select_dirs: List[Path],
    val session_options: Options,
    val deps: Sessions.Deps)
  {
    def session_dirs: List[Path] = dirs ::: select_dirs

    def build_logic(logic: String)
    {
      Build.build_logic(options, logic, build_heap = true, progress = progress,
        dirs = session_dirs, strict = true)
    }

    def session(logic: String, log: Logger = No_Logger): Session =
    {
      build_logic(logic)
      new Session(this, logic, log)
    }
  }

  class Session private[Dump](context: Context, logic: String, log: Logger)
  {
    /* resources */

    private val progress = context.progress

    val resources: Headless.Resources =
      Headless.Resources.make(context.session_options, logic, progress = progress, log = log,
        session_dirs = context.session_dirs,
        include_sessions = context.deps.sessions_structure.imports_topological_order)

    val used_theories: List[Document.Node.Name] =
    {
      for {
        (name, _) <-
          context.deps.used_theories_condition(context.session_options, progress = progress)
        if !resources.session_base.loaded_theory(name.theory)
      } yield name
    }


    /* process */

    def process(process_theory: Args => Unit, unicode_symbols: Boolean = false)
    {
      val session = resources.start_session(progress = progress)


      // asynchronous consumer

      object Consumer
      {
        sealed case class Bad_Theory(
          name: Document.Node.Name,
          status: Document_Status.Node_Status,
          errors: List[String])

        private val consumer_bad_theories = Synchronized(List.empty[Bad_Theory])

        private val consumer =
          Consumer_Thread.fork(name = "dump")(
            consume = (args: (Document.Snapshot, Document_Status.Node_Status)) =>
              {
                val (snapshot, status) = args
                val name = snapshot.node_name
                if (status.ok) {
                  try { process_theory(Args(session, snapshot, status)) }
                  catch {
                    case exn: Throwable if !Exn.is_interrupt(exn) =>
                    val msg = Exn.message(exn)
                    progress.echo("FAILED to process theory " + name)
                    progress.echo_error_message(msg)
                    consumer_bad_theories.change(Bad_Theory(name, status, List(msg)) :: _)
                  }
                }
                else {
                  val msgs =
                    for ((tree, pos) <- snapshot.messages if Protocol.is_error(tree))
                    yield {
                      "Error" + Position.here(pos) + ":\n" +
                        XML.content(Pretty.formatted(List(tree)))
                    }
                  progress.echo("FAILED to process theory " + name)
                  msgs.foreach(progress.echo_error_message)
                  consumer_bad_theories.change(Bad_Theory(name, status, msgs) :: _)
                }
                true
              })

        def apply(snapshot: Document.Snapshot, status: Document_Status.Node_Status): Unit =
          consumer.send((snapshot, status))

        def shutdown(): List[Bad_Theory] =
        {
          consumer.shutdown()
          consumer_bad_theories.value.reverse
        }
      }


      // synchronous body

      try {
        val use_theories_result =
          session.use_theories(used_theories.map(_.theory),
            unicode_symbols = unicode_symbols,
            progress = progress,
            commit = Some(Consumer.apply _))

        val bad_theories = Consumer.shutdown()
        val bad_msgs =
          bad_theories.map(bad =>
            Output.clean_yxml(
              "FAILED theory " + bad.name +
                (if (bad.status.consolidated) "" else ": " + bad.status.percentage + "% finished") +
                (if (bad.errors.isEmpty) "" else bad.errors.mkString("\n", "\n", ""))))

        val pending_msgs =
          use_theories_result.nodes_pending match {
            case Nil => Nil
            case pending => List("Pending theories: " + commas(pending.map(p => p._1.toString)))
          }

        val errors = bad_msgs ::: pending_msgs
        if (errors.nonEmpty) error(errors.mkString("\n\n"))
      }
      finally { session.stop() }
    }
  }


  /* dump */

  val default_output_dir: Path = Path.explode("dump")

  def dump(
    options: Options,
    logic: String,
    aspects: List[Aspect] = Nil,
    progress: Progress = No_Progress,
    log: Logger = No_Logger,
    dirs: List[Path] = Nil,
    select_dirs: List[Path] = Nil,
    output_dir: Path = default_output_dir,
    selection: Sessions.Selection = Sessions.Selection.empty)
  {
    val context =
      Context(options, aspects = aspects, progress = progress, dirs = dirs,
        select_dirs = select_dirs, selection = selection)

    context.session(logic, log = log).process((args: Args) =>
      {
        progress.echo("Processing theory " + args.print_node + " ...")
        val aspect_args =
          Aspect_Args(context.session_options, context.deps, progress, output_dir,
            args.snapshot, args.status)
        aspects.foreach(_.operation(aspect_args))
      })
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
      "v" -> (_ => verbose = true),
      "x:" -> (arg => exclude_sessions = exclude_sessions ::: List(arg)))

      val sessions = getopts(args)

      val progress = new Console_Progress(verbose = verbose)

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
    })
}
