/*  Title:      HOL/Tools/Mirabelle/mirabelle.scala
    Author:     Makarius

Isabelle/Scala front-end for Mirabelle.
*/

package isabelle.mirabelle

import isabelle._


object Mirabelle {
  /* actions and options */

  def action_names(): List[String] = {
    val Pattern = """Mirabelle action: "(\w+)".*""".r
    (for {
      file <-
        File.find_files(Path.explode("~~/src/HOL/Tools/Mirabelle").file,
          pred = file => File.is_ML(file.getName))
      line <- split_lines(File.read(file))
      name <- line match { case Pattern(a) => Some(a) case _ => None }
    } yield name).sorted
  }

  def sledgehammer_options(): List[String] = {
    val Pattern = """val .*K *= *"(.*)" *\(\*(.*)\*\)""".r
    split_lines(File.read(Path.explode("~~/src/HOL/Tools/Mirabelle/mirabelle_sledgehammer.ML"))).
      flatMap(line => line match { case Pattern(a, b) => Some (a + b) case _ => None })
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
    max_jobs: Option[Int] = None,
  ): Build.Results = {
    require(!selection.requirements)
    Isabelle_System.make_directory(output_dir)

    progress.echo("Building required heaps ...")
    val build_results0 =
      Build.build(options, build_heap = true,
        selection = selection.copy(requirements = true), progress = progress, dirs = dirs,
        select_dirs = select_dirs, numa_shuffling = numa_shuffling, max_jobs = max_jobs)

    if (build_results0.ok) {
      val build_options =
        options + "timeout_build=false" +
          ("mirabelle_actions=" + actions.mkString(";")) +
          ("mirabelle_theories=" + theories.mkString(",")) +
          ("mirabelle_output_dir=" + output_dir.implode)


      progress.echo("Running Mirabelle on " + Isabelle_System.identification() + "...")

      def session_setup(session_name: String, session: Session): Unit = {
        session.all_messages +=
          Session.Consumer[Prover.Message]("mirabelle_export") {
            case msg: Prover.Protocol_Output =>
              msg.properties match {
                case Protocol.Export(args) if args.name.startsWith("mirabelle/") =>
                  progress.echo(
                    "Mirabelle export " + quote(args.compound_name) + " (in " + session_name + ")",
                    verbose = true)
                  val yxml = YXML.parse_body(msg.chunk, cache = build_results0.cache)
                  val lines = Pretty.string_of(yxml).trim()
                  val prefix =
                    Export.explode_name(args.name) match {
                      case List("mirabelle", action, "initialize") => action + " initialize "
                      case List("mirabelle", action, "finalize") => action + " finalize   "
                      case List("mirabelle", action, "goal", goal_name, line, offset, cpu_ms) =>
                        action + " goal." + String.format("%-9s", goal_name) + " " + String.format("%5sms", cpu_ms) + " " +
                          args.theory_name + " " + line + ":" + offset + "  "
                      case _ => ""
                    }
                  val body = (if (lines == "") prefix else Library.prefix_lines(prefix, lines)) + "\n"
                  val log_file = output_dir + Path.basic("mirabelle.log")
                  File.append(log_file, body)
                case _ =>
              }
            case _ =>
          }
      }

      Build.build(build_options, clean_build = true,
        selection = selection, progress = progress, dirs = dirs, select_dirs = select_dirs,
        numa_shuffling = numa_shuffling, max_jobs = max_jobs, session_setup = session_setup)
    }
    else build_results0
  }


  /* Isabelle tool wrapper */

  val isabelle_tool = Isabelle_Tool("mirabelle", "testing tool for automated proof tools",
    Scala_Project.here,
    { args =>
      var options = Options.init(specs = Options.Spec.ISABELLE_BUILD_OPTIONS)
      val mirabelle_dry_run = options.check_name("mirabelle_dry_run")
      val mirabelle_max_calls = options.check_name("mirabelle_max_calls")
      val mirabelle_randomize = options.check_name("mirabelle_randomize")
      val mirabelle_stride = options.check_name("mirabelle_stride")
      val mirabelle_timeout = options.check_name("mirabelle_timeout")
      val mirabelle_output_dir = options.check_name("mirabelle_output_dir")
      val mirabelle_parallel_group_size = options.check_name("mirabelle_parallel_group_size")

      var actions: List[String] = Nil
      var base_sessions: List[String] = Nil
      var select_dirs: List[Path] = Nil
      var numa_shuffling = false
      var output_dir = Path.explode(mirabelle_output_dir.default_value)
      var theories: List[String] = Nil
      var exclude_session_groups: List[String] = Nil
      var all_sessions = false
      var dirs: List[Path] = Nil
      var session_groups: List[String] = Nil
      var max_jobs: Option[Int] = None
      var verbose = false
      var exclude_sessions: List[String] = Nil

      val getopts = Getopts("""
Usage: isabelle mirabelle [OPTIONS] [SESSIONS ...]

  Options are:
    -A ACTION    add to list of actions
    -B NAME      include session NAME and all descendants
    -D DIR       include session directory and select its sessions
    -N           cyclic shuffling of NUMA CPU nodes (performance tuning)
    -O DIR       """ + mirabelle_output_dir.description + " (default: " + mirabelle_output_dir.default_value + """)
    -T THEORY    theory restriction: NAME or NAME[FIRST_LINE:LAST_LINE]
    -X NAME      exclude sessions from group NAME and all descendants
    -a           select all sessions
    -d DIR       include session directory
    -g NAME      select session group NAME
    -j INT       maximum number of parallel jobs (default 1)
    -m INT       """ + mirabelle_max_calls.description + " (default " + mirabelle_max_calls.default_value + """)
    -o OPTION    override Isabelle system OPTION (via NAME=VAL or NAME)
    -p INT       """ + mirabelle_parallel_group_size.description + " (default " + mirabelle_parallel_group_size.default_value + """)
    -r INT       """ + mirabelle_randomize.description + " (default " + mirabelle_randomize.default_value + """)
    -s INT       """ + mirabelle_stride.description + " (default " + mirabelle_stride.default_value + """)
    -t SECONDS   """ + mirabelle_timeout.description + " (default " + mirabelle_timeout.default_value + """)
    -v           verbose
    -x NAME      exclude session NAME and all descendants
    -y           """ + mirabelle_dry_run.description + " (default " + mirabelle_dry_run.default_value + """)

  Apply the given ACTIONs at all theories and proof steps of the
  specified sessions.

  The absence of theory restrictions (option -T) means to check all
  theories fully. Otherwise only the named theories are checked.

  Each ACTION is either of the form NAME or NAME [OPTION, ...]
  following Isabelle/Isar outer syntax.

  Available actions are:""" + action_names().mkString("\n    ", "\n    ", "") + """

  For the ACTION "sledgehammer", the usual sledgehammer as well as the following mirabelle-specific OPTIONs are available:""" +
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
        "j:" -> (arg => max_jobs = Some(Value.Nat.parse(arg))),
        "m:" -> (arg => options = options + ("mirabelle_max_calls=" + arg)),
        "o:" -> (arg => options = options + arg),
        "p:" -> (arg => options = options + ("mirabelle_parallel_group_size=" + arg)),
        "r:" -> (arg => options = options + ("mirabelle_randomize=" + arg)),
        "s:" -> (arg => options = options + ("mirabelle_stride=" + arg)),
        "t:" -> (arg => options = options + ("mirabelle_timeout=" + arg)),
        "v" -> (_ => verbose = true),
        "x:" -> (arg => exclude_sessions = exclude_sessions ::: List(arg)),
        "y" -> (arg => options = options + ("mirabelle_dry_run=true")))

      val sessions = getopts(args)
      if (actions.isEmpty) getopts.usage()

      val progress = new Console_Progress(verbose = verbose)

      val start_date = Date.now()

      progress.echo("Started at " + Build_Log.print_date(start_date), verbose = true)

      val results =
        progress.interrupt_handler {
          mirabelle(options, actions, output_dir.absolute,
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
            numa_shuffling = Host.numa_check(progress, numa_shuffling),
            max_jobs = max_jobs)
        }

      val end_date = Date.now()
      val elapsed_time = end_date - start_date

      progress.echo("\nFinished at " + Build_Log.print_date(end_date), verbose = true)

      val total_timing =
        results.sessions.iterator.map(a => results(a).timing).foldLeft(Timing.zero)(_ + _).
          copy(elapsed = elapsed_time)
      progress.echo(total_timing.message_resources)

      sys.exit(results.rc)
    })
}
