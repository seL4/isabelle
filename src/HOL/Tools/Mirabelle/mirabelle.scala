/*  Title:      HOL/Tools/Mirabelle/mirabelle.scala
    Author:     Makarius

Isabelle/Scala front-end for Mirabelle.
*/

package isabelle.mirabelle

import isabelle._


object Mirabelle
{
  /* actions and options */

  def action_names(): List[String] =
  {
    val Pattern = """Mirabelle action: "(\w+)".*""".r
    (for {
      file <-
        File.find_files(Path.explode("~~/src/HOL/Tools/Mirabelle").file,
          pred = _.getName.endsWith(".ML"))
      line <- split_lines(File.read(file))
      name <- line match { case Pattern(a) => Some(a) case _ => None }
    } yield name).sorted
  }

  def sledgehammer_options(): List[String] =
  {
    val Pattern = """val .*K *= *"(.*)" *\(\*(.*)\*\)""".r
    split_lines(File.read(Path.explode("~~/src/HOL/Tools/Mirabelle/mirabelle_sledgehammer.ML"))).
      flatMap(line => line match { case Pattern(a, b) => Some (a + b) case _ => None })
  }


  /* exported log content */

  object Log
  {
    def export_name(index: Int, theory: String = ""): String =
      Export.compound_name(theory, "mirabelle/" + index)

    val separator = "\n------------------\n"

    sealed abstract class Entry { def print: String }

    case class Action(name: String, arguments: Properties.T, body: XML.Body) extends Entry
    {
      def print: String = "action: " + XML.content(body) + separator
    }
    case class Command(name: String, position: Properties.T, body: XML.Body) extends Entry
    {
      def print: String = "\n" + print_head + separator + Pretty.string_of(body)
      def print_head: String =
      {
        val line = Position.Line.get(position)
        val offset = Position.Offset.get(position)
        val loc = line.toString + ":" + offset.toString
        "at " + loc + " (" + name + "):"
      }
    }
    case class Report(result: Properties.T, body: XML.Body) extends Entry
    {
      override def print: String = "\n" + separator + Pretty.string_of(body)
    }

    def entry(export_name: String, xml: XML.Tree): Entry =
      xml match {
        case XML.Elem(Markup("action", (Markup.NAME, name) :: props), body) =>
          Action(name, props, body)
        case XML.Elem(Markup("command", (Markup.NAME, name) :: props), body) =>
          Command(name, props.filter(Markup.position_property), body)
        case XML.Elem(Markup("report", props), body) => Report(props, body)
        case _ => error("Malformed export " + quote(export_name) + "\nbad XML: " + xml)
      }
  }


  /* main mirabelle */

  def mirabelle(
    options: Options,
    actions: List[String],
    output_dir: Path,
    theories: List[String] = Nil,
    selection: Sessions.Selection = Sessions.Selection.empty,
    progress: Progress = new Progress,
    dirs: List[Path] = Nil,
    select_dirs: List[Path] = Nil,
    numa_shuffling: Boolean = false,
    max_jobs: Int = 1,
    verbose: Boolean = false): Build.Results =
  {
    require(!selection.requirements)

    progress.echo("Building required heaps ...")
    val build_results0 =
      Build.build(options, build_heap = true,
        selection = selection.copy(requirements = true), progress = progress, dirs = dirs,
        select_dirs = select_dirs, numa_shuffling = numa_shuffling, max_jobs = max_jobs,
        verbose = verbose)

    if (build_results0.ok) {
      val build_options =
        options + "timeout_build=false" +
          ("mirabelle_actions=" + actions.mkString(";")) +
          ("mirabelle_theories=" + theories.mkString(","))

      progress.echo("Running Mirabelle ...")
      val build_results =
        Build.build(build_options, clean_build = true,
          selection = selection, progress = progress, dirs = dirs, select_dirs = select_dirs,
          numa_shuffling = numa_shuffling, max_jobs = max_jobs, verbose = verbose)

      if (build_results.ok) {
        val structure = Sessions.load_structure(build_options, dirs = dirs, select_dirs = select_dirs)
        val store = Sessions.store(build_options)

        using(store.open_database_context())(db_context =>
        {
          var seen_theories = Set.empty[String]
          for {
            session <- structure.imports_selection(selection).iterator
            session_hierarchy = structure.hierarchy(session)
            theories <- db_context.input_database(session)((db, a) => Some(store.read_theories(db, a)))
            theory <- theories
            if !seen_theories(theory)
            index <- 1 to actions.length
            export <- db_context.read_export(session_hierarchy, theory, Log.export_name(index))
            body = export.uncompressed_yxml
            if body.nonEmpty
          } {
            seen_theories += theory
            val export_name = Log.export_name(index, theory = theory)
            val log = body.map(Log.entry(export_name, _))
            val log_dir = Isabelle_System.make_directory(output_dir + Path.basic(theory))
            val log_file = log_dir + Path.basic("mirabelle" + index).log
            progress.echo("Writing " + log_file)
            File.write(log_file, terminate_lines(log.map(_.print)))
          }
        })
      }

      build_results
    }
    else build_results0
  }


  /* Isabelle tool wrapper */

  val default_output_dir: Path = Path.explode("mirabelle")

  val isabelle_tool = Isabelle_Tool("mirabelle", "testing tool for automated proof tools",
    Scala_Project.here, args =>
  {
    val build_options = Word.explode(Isabelle_System.getenv("ISABELLE_BUILD_OPTIONS"))

    var actions: List[String] = Nil
    var base_sessions: List[String] = Nil
    var select_dirs: List[Path] = Nil
    var numa_shuffling = false
    var output_dir = default_output_dir
    var theories: List[String] = Nil
    var exclude_session_groups: List[String] = Nil
    var all_sessions = false
    var dirs: List[Path] = Nil
    var session_groups: List[String] = Nil
    var max_jobs = 1
    var options = Options.init(opts = build_options)
    var verbose = false
    var exclude_sessions: List[String] = Nil

    val default_stride = options.int("mirabelle_stride")
    val default_timeout = options.seconds("mirabelle_timeout")

    val getopts = Getopts("""
Usage: isabelle mirabelle [OPTIONS] [SESSIONS ...]

  Options are:
    -A ACTION    add to list of actions
    -B NAME      include session NAME and all descendants
    -D DIR       include session directory and select its sessions
    -N           cyclic shuffling of NUMA CPU nodes (performance tuning)
    -O DIR       output directory for log files (default: """ + default_output_dir + """)
    -T THEORY    theory restriction: NAME or NAME[LINE:END_LINE]
    -X NAME      exclude sessions from group NAME and all descendants
    -a           select all sessions
    -d DIR       include session directory
    -g NAME      select session group NAME
    -j INT       maximum number of parallel jobs (default 1)
    -o OPTION    override Isabelle system OPTION (via NAME=VAL or NAME)
    -s INT       run actions on every nth goal (default """ + default_stride + """)
    -t SECONDS   timeout for each action (default """ + default_timeout + """)
    -v           verbose
    -x NAME      exclude session NAME and all descendants

  Apply the given actions at all theories and proof steps of the
  specified sessions.

  The absence of theory restrictions (option -T) means to check all
  theories fully. Otherwise only the named theories are checked.

  Each ACTION is either of the form NAME or NAME [OPTION, ...]
  following Isabelle/Isar outer syntax.

  Available actions are:""" + action_names().mkString("\n    ", "\n    ", "") + """

  For the ACTION "sledgehammer", the following OPTIONs are available:""" +
      sledgehammer_options().mkString("\n    ", "\n    ", "\n"),
      "A:" -> (arg => actions = actions ::: List(arg)),
      "B:" -> (arg => base_sessions = base_sessions ::: List(arg)),
      "D:" -> (arg => select_dirs = select_dirs ::: List(Path.explode(arg))),
      "N" -> (_ => numa_shuffling = true),
      "O:" -> (arg => output_dir = Path.explode(arg)),
      "T:" -> (arg => theories = theories ::: List(arg)),
      "X:" -> (arg => exclude_session_groups = exclude_session_groups ::: List(arg)),
      "a" -> (_ => all_sessions = true),
      "d:" -> (arg => dirs = dirs ::: List(Path.explode(arg))),
      "g:" -> (arg => session_groups = session_groups ::: List(arg)),
      "j:" -> (arg => max_jobs = Value.Int.parse(arg)),
      "o:" -> (arg => options = options + arg),
      "s:" -> (arg => options = options + ("mirabelle_stride=" + arg)),
      "t:" -> (arg => options = options + ("mirabelle_timeout=" + arg)),
      "v" -> (_ => verbose = true),
      "x:" -> (arg => exclude_sessions = exclude_sessions ::: List(arg)))

    val sessions = getopts(args)
    if (actions.isEmpty) getopts.usage()

    val progress = new Console_Progress(verbose = verbose)

    val start_date = Date.now()

    if (verbose) {
      progress.echo("Started at " + Build_Log.print_date(start_date))
    }

    val results =
      progress.interrupt_handler {
        mirabelle(options, actions, output_dir,
          theories = theories,
          selection = Sessions.Selection(
            all_sessions = all_sessions,
            base_sessions = base_sessions,
            exclude_session_groups = exclude_session_groups,
            exclude_sessions = exclude_sessions,
            session_groups = session_groups,
            sessions = sessions),
          progress = progress,
          dirs = dirs,
          select_dirs = select_dirs,
          numa_shuffling = NUMA.enabled_warning(progress, numa_shuffling),
          max_jobs = max_jobs,
          verbose = verbose)
      }

    val end_date = Date.now()
    val elapsed_time = end_date.time - start_date.time

    if (verbose) {
      progress.echo("\nFinished at " + Build_Log.print_date(end_date))
    }

    val total_timing =
      results.sessions.iterator.map(a => results(a).timing).foldLeft(Timing.zero)(_ + _).
        copy(elapsed = elapsed_time)
    progress.echo(total_timing.message_resources)

    sys.exit(results.rc)
  })
}
