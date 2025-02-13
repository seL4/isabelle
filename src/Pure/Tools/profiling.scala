/*  Title:      Pure/Tools/profiling.scala
    Author:     Makarius

Build sessions for profiling of ML heap content.
*/

package isabelle


import java.util.Locale


object Profiling {
  /* percentage: precision in permille */

  def percentage(a: Long, b: Long): Percentage =
    new Percentage(if (b == 0L) 0 else ((a.toDouble / b.toDouble) * 1000.0).round.toInt)

  def percentage(a: Int, b: Int): Percentage = percentage(a.toLong, b.toLong)

  def percentage_space(a: Space, b: Space): Percentage = percentage(a.bytes, b.bytes)

  final class Percentage private[Profiling](val permille: Int) extends AnyVal {
    def percent: Double = permille.toDouble / 10

    override def toString: String = (permille / 10).toString + "." + (permille % 10).toString + "%"
  }


  /* session statistics */

  sealed case class Session_Statistics(
    theories: Int = 0,
    garbage_theories: Int = 0,
    locales: Int = 0,
    locale_thms: Int = 0,
    global_thms: Int = 0,
    sizeof_thys_id: Space = Space.zero,
    sizeof_thms_id: Space = Space.zero,
    sizeof_terms: Space = Space.zero,
    sizeof_types: Space = Space.zero,
    sizeof_names: Space = Space.zero,
    sizeof_spaces: Space = Space.zero)

  object Statistics {
    private val encode_args: XML.Encode.T[List[String]] =
      (args: List[String]) =>
        { import XML.Encode._; list(string)(args) }

    private val decode_result: XML.Decode.T[Session_Statistics] =
      (body: XML.Body) =>
        {
          val (a, (b, (c, (d, (e, (f, (g, (h, (i, (j, k)))))))))) = {
            import XML.Decode._
            pair(int, pair(int, pair(int, pair(int, pair(int,
              pair(long, pair(long, pair(long, pair(long, pair(long, long))))))))))(body)
          }
          Session_Statistics(
            theories = a,
            garbage_theories = b,
            locales = c,
            locale_thms = d,
            global_thms = e,
            sizeof_thys_id = Space.bytes(f),
            sizeof_thms_id = Space.bytes(g),
            sizeof_terms = Space.bytes(h),
            sizeof_types = Space.bytes(i),
            sizeof_names = Space.bytes(j),
            sizeof_spaces = Space.bytes(k))
        }

    def make(
      store: Store,
      session_background: Sessions.Background,
      parent: Option[Statistics] = None
    ): Statistics = {
      val session_base = session_background.base
      val session_name = session_base.session_name

      val session = {
        val args = session_base.used_theories.map(p => p._1.theory)
        val eval_args =
          List("--eval", "use_thy " + ML_Syntax.print_string_bytes("~~/src/Tools/Profiling"))
        Isabelle_System.with_tmp_dir("profiling") { dir =>
          val put_env = List("ISABELLE_PROFILING" -> dir.implode)
          File.write(dir + Path.explode("args.yxml"), YXML.string_of_body(encode_args(args)))
          val session_heaps =
            ML_Process.session_heaps(store, session_background, logic = session_name)
          ML_Process(store.options, session_background, session_heaps, args = eval_args,
            env = Isabelle_System.settings(put_env)).result().check
          decode_result(YXML.parse_body(Bytes.read(dir + Path.explode("result.yxml"))))
        }
      }

      new Statistics(parent = parent, session = session_name,
        theories = session.theories,
        garbage_theories = session.garbage_theories,
        locales = session.locales,
        locale_thms = session.locale_thms,
        global_thms = session.global_thms,
        heap_size = File.space(store.get_session(session_name).the_heap),
        thys_id_size = session.sizeof_thys_id,
        thms_id_size = session.sizeof_thms_id,
        terms_size = session.sizeof_terms,
        types_size = session.sizeof_types,
        names_size = session.sizeof_names,
        spaces_size = session.sizeof_spaces)
    }

    val empty: Statistics = new Statistics()

    val header0: List[String] =
      List(
        "named_theories",
        "total_theories",
        "locales",
        "locale_thms",
        "global_thms",
        "locale_thms%",
        "global_thms%",
        "heap_size",
        "thys_id_size%",
        "thms_id_size%",
        "terms_size%",
        "types_size%",
        "names_size%",
        "spaces_size%")

    def header: List[String] =
      "session" :: header0.flatMap(a => List(a, Symbol.decode("""\<Sum>""") + a))
  }

  final class Statistics private(
    val parent: Option[Statistics] = None,
    val session: String = "",
    val theories: Int = 0,
    val garbage_theories: Int = 0,
    val locales: Int = 0,
    val locale_thms: Int = 0,
    val global_thms: Int = 0,
    val heap_size: Space = Space.zero,
    val thys_id_size: Space = Space.zero,
    val thms_id_size: Space = Space.zero,
    val terms_size: Space = Space.zero,
    val types_size: Space = Space.zero,
    val names_size: Space = Space.zero,
    val spaces_size: Space = Space.zero
  ) {
    private def print_total_theories: String =
      if (theories == 0) "0"
      else {
        val x = (theories + garbage_theories).toDouble / theories
        String.format(Locale.ROOT, "%.1f", x.asInstanceOf[AnyRef])
      }

    private def size_percentage(space: Space): Percentage =
      percentage_space(space, heap_size)

    private def thms_percentage(thms: Int): Percentage =
      percentage(thms, locale_thms + global_thms)

    val fields0: List[Any] =
      List(
        theories,
        print_total_theories,
        locales,
        locale_thms,
        global_thms,
        thms_percentage(locale_thms).toString,
        thms_percentage(global_thms).toString,
        heap_size.print,
        size_percentage(thys_id_size).toString,
        size_percentage(thms_id_size).toString,
        size_percentage(terms_size).toString,
        size_percentage(types_size).toString,
        size_percentage(names_size).toString,
        size_percentage(spaces_size).toString)

    def fields: List[Any] =
      session :: fields0.zipWithIndex.flatMap({ case (a, i) => List(a, cumulative.fields0(i)) })

    lazy val cumulative: Statistics =
      parent match {
        case None => this
        case Some(other) =>
          new Statistics(parent = None,
            session = session,
            theories = other.cumulative.theories + theories,
            garbage_theories = other.cumulative.garbage_theories + garbage_theories,
            locales = other.cumulative.locales + locales,
            locale_thms = other.cumulative.locale_thms + locale_thms,
            global_thms = other.cumulative.global_thms + global_thms,
            heap_size = other.cumulative.heap_size + heap_size,
            thys_id_size = other.cumulative.thys_id_size + thys_id_size,
            thms_id_size = other.cumulative.thms_id_size + thms_id_size,
            terms_size = other.cumulative.terms_size + terms_size,
            types_size = other.cumulative.types_size + types_size,
            names_size = other.cumulative.names_size + names_size,
            spaces_size = other.cumulative.spaces_size + spaces_size)
      }

    override def toString: String = "Statistics(" + session + ")"
  }


  /* profiling results */

  sealed case class Results(build_results: Build.Results, sessions: List[Statistics]) {
    def output(
      output_dir: Path = default_output_dir,
      progress: Progress = new Progress
    ): Unit = {
      progress.echo("Output directory " + output_dir.absolute)
      Isabelle_System.make_directory(output_dir)
      val csv_records = for (session <- sessions) yield CSV.Record(session.fields:_*)
      CSV.File("sessions", Statistics.header, csv_records).write(output_dir)
    }
  }

  def profiling(
    options: Options,
    selection: Sessions.Selection = Sessions.Selection.empty,
    progress: Progress = new Progress,
    dirs: List[Path] = Nil,
    select_dirs: List[Path] = Nil,
    numa_shuffling: Boolean = false,
    max_jobs: Option[Int] = None
  ): Results = {
    /* sessions structure */

    val sessions_dirs = dirs ::: select_dirs

    val sessions_structure =
      Sessions.load_structure(options, dirs = dirs, select_dirs = select_dirs)

    val selected_sessions = sessions_structure.imports_selection(selection)
    val cumulative_sessions = sessions_structure.build_requirements(selected_sessions)

    val sessions_selection = Sessions.Selection(sessions = selected_sessions)


    /* build session */

    val store = Store(options)

    def build(
      selection: Sessions.Selection,
      build_options: Options = options,
      build_heap: Boolean = false,
      clean_build: Boolean = false
    ): Build.Results = {
      val results =
        Build.build(build_options, progress = progress,
          selection = selection, build_heap = build_heap, clean_build = clean_build,
          dirs = sessions_dirs, numa_shuffling = numa_shuffling, max_jobs = max_jobs)

      if (results.ok) results else error("Build failed")
    }


    /* session builds and profiling */

    progress.echo("Build session requirements:")
    build(sessions_selection.copy(requirements = true), build_heap = true)
    progress.echo("DONE")

    progress.echo("Build sessions:")
    val build_results =
      build(sessions_selection,
        build_options = options + "context_theory_tracing",
        build_heap = true,
        clean_build = true)
    progress.echo("DONE")

    val sessions = {
      var seen = Map.empty[String, Statistics]
      for (session_name <- cumulative_sessions)
      yield {
        progress.echo("Profiling " + session_name + " ...")
        val parent =
          for {
            info <- sessions_structure.get(session_name)
            parent_name <- info.parent
            parent_stats <- seen.get(parent_name)
          } yield parent_stats
        val stats =
          Statistics.make(store,
            build_results.deps.background(session_name),
            parent = parent)
        seen += (session_name -> stats)
        stats
      }
    }
    progress.echo("DONE")

    Results(build_results, sessions)
  }


  /* Isabelle tool wrapper */

  val default_output_dir: Path = Path.explode("profiling")

  val isabelle_tool =
    Isabelle_Tool("profiling", "build sessions for profiling of ML heap content",
      Scala_Project.here, { args =>
        var base_sessions: List[String] = Nil
        var select_dirs: List[Path] = Nil
        var numa_shuffling = false
        var output_dir = default_output_dir
        var exclude_session_groups: List[String] = Nil
        var all_sessions = false
        var dirs: List[Path] = Nil
        var session_groups: List[String] = Nil
        var max_jobs: Option[Int] = None
        var options = Options.init(specs = Options.Spec.ISABELLE_BUILD_OPTIONS)
        var verbose = false
        var exclude_sessions: List[String] = Nil

        val getopts = Getopts("""
Usage: isabelle profiling [OPTIONS] [SESSIONS ...]

  Options are:
    -B NAME      include session NAME and all descendants
    -D DIR       include session directory and select its sessions
    -N           cyclic shuffling of NUMA CPU nodes (performance tuning)
    -O DIR       output directory (default: """ + default_output_dir + """)
    -X NAME      exclude sessions from group NAME and all descendants
    -a           select all sessions
    -d DIR       include session directory
    -g NAME      select session group NAME
    -j INT       maximum number of parallel jobs (default 1)
    -o OPTION    override Isabelle system OPTION (via NAME=VAL or NAME)
    -v           verbose
    -x NAME      exclude session NAME and all descendants

  Build specified sessions, with options similar to "isabelle build" and
  implicit modifications for profiling of ML heap content.""",
          "B:" -> (arg => base_sessions = base_sessions ::: List(arg)),
          "D:" -> (arg => select_dirs = select_dirs ::: List(Path.explode(arg))),
          "N" -> (_ => numa_shuffling = true),
          "O:" -> (arg => output_dir = Path.explode(arg)),
          "X:" -> (arg => exclude_session_groups = exclude_session_groups ::: List(arg)),
          "a" -> (_ => all_sessions = true),
          "d:" -> (arg => dirs = dirs ::: List(Path.explode(arg))),
          "g:" -> (arg => session_groups = session_groups ::: List(arg)),
          "j:" -> (arg => max_jobs = Some(Value.Nat.parse(arg))),
          "o:" -> (arg => options = options + arg),
          "v" -> (_ => verbose = true),
          "x:" -> (arg => exclude_sessions = exclude_sessions ::: List(arg)))

        val sessions = getopts(args)

        val progress = new Console_Progress(verbose = verbose)

        val results =
          progress.interrupt_handler {
            profiling(options,
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

        results.output(output_dir = output_dir.absolute, progress = progress)
      })
}
