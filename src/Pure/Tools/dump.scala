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
    node_name: Document.Node.Name,
    node_status: Protocol.Node_Status,
    snapshot: Document.Snapshot)
  {
    def write(file_name: Path, bytes: Bytes)
    {
      val path = output_dir + Path.basic(node_name.theory) + file_name
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

  val known_aspects =
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
        }, options = List("editor_presentation")),
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


  /* dump */

  val default_output_dir = Path.explode("dump")

  def dump(options: Options, logic: String,
    aspects: List[Aspect] = Nil,
    progress: Progress = No_Progress,
    log: Logger = No_Logger,
    dirs: List[Path] = Nil,
    select_dirs: List[Path] = Nil,
    output_dir: Path = default_output_dir,
    verbose: Boolean = false,
    system_mode: Boolean = false,
    selection: Sessions.Selection = Sessions.Selection.empty): Process_Result =
  {
    if (Build.build_logic(options, logic, progress = progress, dirs = dirs,
      system_mode = system_mode) != 0) error(logic + " FAILED")

    val dump_options =
      (options.int.update("completion_limit", 0).bool.update("ML_statistics", false) /: aspects)(
        { case (opts, aspect) => (opts /: aspect.options)(_ + _) })


    /* dependencies */

    val deps =
      Sessions.load_structure(dump_options, dirs = dirs, select_dirs = select_dirs).
        selection_deps(selection)

    val include_sessions =
      deps.sessions_structure.imports_topological_order

    val use_theories =
      deps.sessions_structure.build_topological_order.
        flatMap(session_name => deps.session_bases(session_name).used_theories.map(_.theory))


    /* session */

    val session =
      Thy_Resources.start_session(dump_options, logic, session_dirs = dirs,
        include_sessions = include_sessions, progress = progress, log = log)

    val theories_result = session.use_theories(use_theories, progress = progress)
    val session_result = session.stop()


    /* dump aspects */

    for ((node_name, node_status) <- theories_result.nodes) {
      val snapshot = theories_result.snapshot(node_name)
      val aspect_args =
        Aspect_Args(dump_options, progress, deps, output_dir, node_name, node_status, snapshot)
      aspects.foreach(_.operation(aspect_args))
    }

    session_result
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
      "l:" -> (arg => logic = arg),
      "g:" -> (arg => session_groups = session_groups ::: List(arg)),
      "o:" -> (arg => options = options + arg),
      "s" -> (_ => system_mode = true),
      "v" -> (_ => verbose = true),
      "x:" -> (arg => exclude_sessions = exclude_sessions ::: List(arg)))

      val sessions = getopts(args)

      val progress = new Console_Progress(verbose = verbose)

      val result =
        progress.interrupt_handler {
          dump(options, logic,
            aspects = aspects,
            progress = progress,
            dirs = dirs,
            select_dirs = select_dirs,
            output_dir = output_dir,
            verbose = verbose,
            selection = Sessions.Selection(
              requirements = requirements,
              all_sessions = all_sessions,
              base_sessions = base_sessions,
              exclude_session_groups = exclude_session_groups,
              exclude_sessions = exclude_sessions,
              session_groups = session_groups,
              sessions = sessions))
        }

      progress.echo(result.timing.message_resources)

      sys.exit(result.rc)
    })
}
