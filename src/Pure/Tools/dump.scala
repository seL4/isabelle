/*  Title:      Pure/Tools/dump.scala
    Author:     Makarius

Dump cumulative PIDE session database.
*/

package isabelle

import java.io.{BufferedWriter, FileOutputStream, OutputStreamWriter}


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
    def write_path(file_name: Path): Path =
    {
      val path = output_dir + Path.basic(snapshot.node_name.theory) + file_name
      Isabelle_System.make_directory(path.dir)
      path
    }

    def write(file_name: Path, bytes: Bytes): Unit =
      Bytes.write(write_path(file_name), bytes)

    def write(file_name: Path, text: String): Unit =
      write(file_name, Bytes(text))

    def write(file_name: Path, body: XML.Body): Unit =
      using(File.writer(write_path(file_name).file))(
        writer => YXML.traversal(s => writer.write(Symbol.encode(s)), body))
  }

  sealed case class Aspect(name: String, description: String, operation: Aspect_Args => Unit,
    options: List[String] = Nil)
  {
    override def toString: String = name
  }

  val known_aspects: List[Aspect] =
    List(
      Aspect("markup", "PIDE markup (YXML format)",
        args => args.write(Path.explode(Export.MARKUP), args.snapshot.xml_markup())),
      Aspect("messages", "output messages (YXML format)",
        args => args.write(Path.explode(Export.MESSAGES), args.snapshot.messages.map(_._1))),
      Aspect("latex", "generated LaTeX source",
        args =>
          for {
            entry <- args.snapshot.exports
            if entry.name_has_prefix(Export.DOCUMENT_PREFIX)
          } args.write(Path.explode(entry.name), entry.uncompressed)),
      Aspect("theory", "foundational theory content",
        args =>
          for {
            entry <- args.snapshot.exports
            if entry.name_has_prefix(Export.THEORY_PREFIX)
          } args.write(Path.explode(entry.name), entry.uncompressed),
        options = List("export_theory"))
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
      progress: Progress = new Progress,
      dirs: List[Path] = Nil,
      select_dirs: List[Path] = Nil,
      selection: Sessions.Selection = Sessions.Selection.empty,
      pure_base: Boolean = false,
      skip_base: Boolean = false): Context =
    {
      val session_options: Options =
      {
        val options0 = if (NUMA.enabled) NUMA.policy_options(options) else options
        val options1 =
          options0 +
            "parallel_proofs=0" +
            "completion_limit=0" +
            "editor_tracing_messages=0" +
            "editor_presentation"
        aspects.foldLeft(options1) { case (opts, aspect) => aspect.options.foldLeft(opts)(_ + _) }
      }

      val sessions_structure: Sessions.Structure =
        Sessions.load_structure(session_options, dirs = dirs, select_dirs = select_dirs).
          selection(selection)

      {
        val selection_size = sessions_structure.build_graph.size
        if (selection_size > 1) progress.echo("Loading " + selection_size + " sessions ...")
      }

      val deps: Sessions.Deps =
        Sessions.deps(sessions_structure, progress = progress).check_errors

      new Context(options, progress, dirs, select_dirs, pure_base, skip_base, session_options, deps)
    }
  }

  class Context private(
    val options: Options,
    val progress: Progress,
    val dirs: List[Path],
    val select_dirs: List[Path],
    val pure_base: Boolean,
    val skip_base: Boolean,
    val session_options: Options,
    val deps: Sessions.Deps)
  {
    context =>

    def session_dirs: List[Path] = dirs ::: select_dirs

    def build_logic(logic: String): Unit =
    {
      Build.build_logic(options, logic, build_heap = true, progress = progress,
        dirs = session_dirs, strict = true)
    }

    def sessions(
      logic: String = default_logic,
      log: Logger = No_Logger): List[Session] =
    {
      /* partitions */

      def session_info(session_name: String): Sessions.Info =
        deps.sessions_structure(session_name)

      val session_graph = deps.sessions_structure.build_graph
      val all_sessions = session_graph.topological_order

      val afp_sessions =
        (for (name <- all_sessions if session_info(name).is_afp) yield name).toSet

      val afp_bulky_sessions =
        (for (name <- all_sessions if session_info(name).is_afp_bulky) yield name).toList

      val base_sessions =
        session_graph.all_preds_rev(List(logic).filter(session_graph.defined))

      val proof_sessions =
        session_graph.all_succs(
          for (name <- all_sessions if session_info(name).record_proofs) yield name)


      /* resulting sessions */

      def make_session(
        selected_sessions: List[String],
        session_logic: String = logic,
        strict: Boolean = false,
        record_proofs: Boolean = false): List[Session] =
      {
        if (selected_sessions.isEmpty && !strict) Nil
        else List(new Session(context, session_logic, log, selected_sessions, record_proofs))
      }

      val PURE = isabelle.Thy_Header.PURE

      val base =
        if ((logic == PURE && !pure_base) || skip_base) Nil
        else make_session(base_sessions, session_logic = PURE, strict = logic == PURE)

      val main =
        make_session(
          session_graph.topological_order.filterNot(name =>
            afp_sessions.contains(name) ||
            base_sessions.contains(name) ||
            proof_sessions.contains(name)))

      val proofs = make_session(proof_sessions, session_logic = PURE, record_proofs = true)

      val afp =
        if (afp_sessions.isEmpty) Nil
        else {
          val (part1, part2) =
          {
            val graph = session_graph.restrict(afp_sessions -- afp_bulky_sessions)
            val force_partition1 = AFP.force_partition1.filter(graph.defined)
            val force_part1 = graph.all_preds(graph.all_succs(force_partition1)).toSet
            graph.keys.partition(a => force_part1(a) || graph.is_isolated(a))
          }
          List(part1, part2, afp_bulky_sessions).flatMap(make_session(_))
        }

      proofs ::: base ::: main ::: afp
    }


    /* processed theories */

    private val processed_theories = Synchronized(Set.empty[String])

    def process_theory(theory: String): Boolean =
      processed_theories.change_result(processed => (!processed(theory), processed + theory))


    /* errors */

    private val errors = Synchronized(List.empty[String])

    def add_errors(more_errs: List[String]): Unit =
    {
      errors.change(errs => errs ::: more_errs)
    }

    def check_errors: Unit =
    {
      val errs = errors.value
      if (errs.nonEmpty) error(errs.mkString("\n\n"))
    }
  }

  class Session private[Dump](
    val context: Context,
    val logic: String,
    log: Logger,
    selected_sessions: List[String],
    record_proofs: Boolean)
  {
    /* resources */

    val options: Options =
      if (record_proofs) context.session_options + "record_proofs=2"
      else context.session_options

    private def deps = context.deps
    private def progress = context.progress

    val resources: Headless.Resources =
      Headless.Resources.make(options, logic, progress = progress, log = log,
        session_dirs = context.session_dirs,
        include_sessions = deps.sessions_structure.imports_topological_order)

    val used_theories: List[Document.Node.Name] =
    {
      for {
        session_name <-
          deps.sessions_structure.build_graph.restrict(selected_sessions.toSet).topological_order
        (name, theory_options) <- deps(session_name).used_theories
        if !resources.session_base.loaded_theory(name.theory)
        if {
          def warn(msg: String): Unit =
            progress.echo_warning("Skipping theory " + name + "  (" + msg + ")")

          val conditions =
            space_explode(',', theory_options.string("condition")).
              filter(cond => Isabelle_System.getenv(cond) == "")
          if (conditions.nonEmpty) {
            warn("undefined " + conditions.mkString(", "))
            false
          }
          else if (options.bool("skip_proofs") && !theory_options.bool("skip_proofs")) {
            warn("option skip_proofs")
            false
          }
          else true
        }
      } yield name
    }


    /* process */

    def process(process_theory: Args => Unit, unicode_symbols: Boolean = false): Unit =
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
                  try {
                    if (context.process_theory(name.theory)) {
                      process_theory(Args(session, snapshot, status))
                    }
                  }
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
                    for ((elem, pos) <- snapshot.messages if Protocol.is_error(elem))
                    yield {
                      "Error" + Position.here(pos) + ":\n" +
                        XML.content(Pretty.formatted(List(elem)))
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
            commit = Some(Consumer.apply))

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

        context.add_errors(bad_msgs ::: pending_msgs)
      }
      finally { session.stop() }
    }
  }


  /* dump */

  val default_output_dir: Path = Path.explode("dump")
  val default_logic: String = Thy_Header.PURE

  def dump(
    options: Options,
    logic: String,
    aspects: List[Aspect] = Nil,
    progress: Progress = new Progress,
    log: Logger = No_Logger,
    dirs: List[Path] = Nil,
    select_dirs: List[Path] = Nil,
    output_dir: Path = default_output_dir,
    selection: Sessions.Selection = Sessions.Selection.empty): Unit =
  {
    val context =
      Context(options, aspects = aspects, progress = progress, dirs = dirs,
        select_dirs = select_dirs, selection = selection)

    context.build_logic(logic)

    for (session <- context.sessions(logic = logic, log = log)) {
      session.process((args: Args) =>
        {
          progress.echo("Processing theory " + args.print_node + " ...")
          val aspect_args =
            Aspect_Args(session.options, context.deps, progress, output_dir,
              args.snapshot, args.status)
          aspects.foreach(_.operation(aspect_args))
        })
    }

    context.check_errors
  }


  /* Isabelle tool wrapper */

  val isabelle_tool =
    Isabelle_Tool("dump", "dump cumulative PIDE session database", Scala_Project.here, args =>
    {
      var aspects: List[Aspect] = known_aspects
      var base_sessions: List[String] = Nil
      var select_dirs: List[Path] = Nil
      var output_dir = default_output_dir
      var requirements = false
      var exclude_session_groups: List[String] = Nil
      var all_sessions = false
      var logic = default_logic
      var dirs: List[Path] = Nil
      var session_groups: List[String] = Nil
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
    -R           refer to requirements of selected sessions
    -X NAME      exclude sessions from group NAME and all descendants
    -a           select all sessions
    -b NAME      base logic image (default """ + isabelle.quote(default_logic) + """)
    -d DIR       include session directory
    -g NAME      select session group NAME
    -o OPTION    override Isabelle system OPTION (via NAME=VAL or NAME)
    -v           verbose
    -x NAME      exclude session NAME and all descendants

  Dump cumulative PIDE session database, with the following aspects:

""" + Library.indent_lines(4, show_aspects) + "\n",
      "A:" -> (arg => aspects = Library.distinct(space_explode(',', arg)).map(the_aspect)),
      "B:" -> (arg => base_sessions = base_sessions ::: List(arg)),
      "D:" -> (arg => select_dirs = select_dirs ::: List(Path.explode(arg))),
      "O:" -> (arg => output_dir = Path.explode(arg)),
      "R" -> (_ => requirements = true),
      "X:" -> (arg => exclude_session_groups = exclude_session_groups ::: List(arg)),
      "a" -> (_ => all_sessions = true),
      "b:" -> (arg => logic = arg),
      "d:" -> (arg => dirs = dirs ::: List(Path.explode(arg))),
      "g:" -> (arg => session_groups = session_groups ::: List(arg)),
      "o:" -> (arg => options = options + arg),
      "v" -> (_ => verbose = true),
      "x:" -> (arg => exclude_sessions = exclude_sessions ::: List(arg)))

      val sessions = getopts(args)

      val progress = new Console_Progress(verbose = verbose)

      val start_date = Date.now()

      progress.echo_if(verbose, "Started at " + Build_Log.print_date(start_date))

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

      val end_date = Date.now()
      val timing = end_date.time - start_date.time

      progress.echo_if(verbose, "\nFinished at " + Build_Log.print_date(end_date))
      progress.echo(timing.message_hms + " elapsed time")
    })
}
