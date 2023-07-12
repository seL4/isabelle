/*  Title:      Pure/Tools/profiling_report.scala
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


  /* session and theory statistics */

  object Theory_Statistics {
    def sum(name: String, theories: List[Theory_Statistics]): Theory_Statistics =
      theories.foldLeft(Theory_Statistics(name = name))(_ + _)

    val header: List[String] =
      List("name", "locales", "locale_thms", "global_thms",
        "locale_thms_percentage", "global_thms_percentage")
  }

  sealed case class Theory_Statistics(
    name: String = "",
    locales: Int = 0,
    locale_thms: Int = 0,
    global_thms: Int = 0
  ) {
    def + (other: Theory_Statistics): Theory_Statistics =
      copy(
        locales = other.locales + locales,
        locale_thms = other.locale_thms + locale_thms,
        global_thms = other.global_thms + global_thms)

    def thms: Int = locale_thms + global_thms

    def fields: List[Any] =
      List(name, locales, locale_thms, global_thms,
        percentage(locale_thms, thms), percentage(global_thms, thms))
  }

  sealed case class Session_Statistics(
    sizeof_thys_id: Space = Space.zero,
    sizeof_thms_id: Space = Space.zero,
    sizeof_terms: Space = Space.zero,
    sizeof_types: Space = Space.zero,
    sizeof_spaces: Space = Space.zero)

  object Statistics {
    private val encode_args: XML.Encode.T[List[String]] =
      (args: List[String]) =>
        { import XML.Encode._; list(string)(args) }

    private val decode_theories_result: XML.Decode.T[List[Theory_Statistics]] =
      (body: XML.Body) =>
        { import XML.Decode._; list(pair(string, pair(int, pair(int, int))))(body) } map {
          case (a, (b, (c, d))) =>
            Theory_Statistics(
              name = a,
              locales = b,
              locale_thms = c,
              global_thms = d)
        }

    private val decode_session_result: XML.Decode.T[Session_Statistics] =
      (body: XML.Body) =>
        {
          val (a, (b, (c, (d, e)))) = {
            import XML.Decode._
            pair(long, pair(long, pair(long, pair(long, long))))(body)
          }
          Session_Statistics(
            sizeof_thys_id = Space.bytes(a),
            sizeof_thms_id = Space.bytes(b),
            sizeof_terms = Space.bytes(c),
            sizeof_types = Space.bytes(d),
            sizeof_spaces = Space.bytes(e))
        }
    private val decode_result: XML.Decode.T[(List[Theory_Statistics], Session_Statistics)] =
      (body: XML.Body) =>
        { import XML.Decode._; pair(decode_theories_result, decode_session_result)(body) }

    def make(
      store: Store,
      session_background: Sessions.Background,
      parent: Option[Statistics] = None,
      anonymous_theories: Boolean = false
    ): Statistics = {
      val session_base = session_background.base
      val session_name = session_base.session_name
      val sessions_structure = session_background.sessions_structure

      val theories_name = session_base.used_theories.map(p => p._1.theory)
      val theories_index =
        Map.from(
          for ((name, i) <- theories_name.zipWithIndex)
            yield name -> String.format(Locale.ROOT, "%s.%04d", session_name, i + 1))

      val (theories0, session) = {
        val args = theories_name
        val eval_args =
          List("--eval", "use_thy " + ML_Syntax.print_string_bytes("~~/src/Tools/Profiling"))
        Isabelle_System.with_tmp_dir("profiling") { dir =>
          val put_env = List("ISABELLE_PROFILING" -> dir.implode)
          File.write(dir + Path.explode("args.yxml"), YXML.string_of_body(encode_args(args)))
          val session_heaps =
            ML_Process.session_heaps(store, session_background, logic = session_name)
          ML_Process(store.options, session_background, session_heaps, args = eval_args,
            env = Isabelle_System.settings(put_env)).result().check
          decode_result(YXML.parse_body(File.read(dir + Path.explode("result.yxml"))))
        }
      }

      val theories =
        if (anonymous_theories) theories0.map(a => a.copy(name = theories_index(a.name)))
        else theories0

      new Statistics(parent = parent, session_name = session_name, theories = theories,
        heap_size = Space.bytes(store.the_heap(session_name).file.length),
        thys_id_size = session.sizeof_thys_id,
        thms_id_size = session.sizeof_thms_id,
        terms_size = session.sizeof_terms,
        types_size = session.sizeof_types,
        spaces_size = session.sizeof_spaces)
    }

    val empty: Statistics = new Statistics()

    val header: List[String] =
      Theory_Statistics.header :::
        List("heap_size",
          "thys_id_size_percentage",
          "thms_id_size_percentage",
          "terms_size_percentage",
          "types_size_percentage",
          "spaces_size_percentage")
    val header_cumulative: List[String] = header ::: header.tail.map(_ + "_cumulative")
  }

  final class Statistics private(
    val parent: Option[Statistics] = None,
    val session_name: String = "",
    val theories: List[Theory_Statistics] = Nil,
    val heap_size: Space = Space.zero,
    val thys_id_size: Space = Space.zero,
    val thms_id_size: Space = Space.zero,
    val terms_size: Space = Space.zero,
    val types_size: Space = Space.zero,
    val spaces_size: Space = Space.zero
  ) {
    private def size_percentage(space: Space): Percentage =
      percentage_space(space, heap_size)

    def fields: List[Any] =
      session.fields :::
        List(heap_size.print,
          size_percentage(thys_id_size).toString,
          size_percentage(thms_id_size).toString,
          size_percentage(terms_size).toString,
          size_percentage(types_size).toString,
          size_percentage(spaces_size).toString)
    def fields_cumulative: List[Any] = fields ::: cumulative.fields.tail

    lazy val session: Theory_Statistics =
      Theory_Statistics.sum(session_name, theories)

    lazy val cumulative: Statistics =
      parent match {
        case None => this
        case Some(other) =>
          new Statistics(parent = None,
            session_name = session_name,
            theories = other.cumulative.theories ::: theories,
            heap_size = other.cumulative.heap_size + heap_size,
            thys_id_size = other.cumulative.thys_id_size + thys_id_size,
            thms_id_size = other.cumulative.thms_id_size + thms_id_size,
            terms_size = other.cumulative.terms_size + terms_size,
            types_size = other.cumulative.types_size + types_size,
            spaces_size = other.cumulative.spaces_size + spaces_size)
      }

    override def toString: String = "Statistics(" + session_name + ")"
  }


  /* profiling results */

  sealed case class Results(build_results: Build.Results, sessions: List[Statistics]) {
    def output(
      output_dir: Path = default_output_dir,
      progress: Progress = new Progress
    ): Unit = {
      progress.echo("Output directory " + output_dir.absolute)
      Isabelle_System.make_directory(output_dir)

      val sessions_records =
        for (stats <- sessions) yield {
          CSV.File("session_" + stats.session_name, Theory_Statistics.header,
            stats.theories.map(thy => CSV.Record(thy.fields:_*))).write(output_dir)
          CSV.Record(stats.fields_cumulative:_*)
        }
      CSV.File("all_sessions", Statistics.header_cumulative, sessions_records).write(output_dir)
    }
  }

  def profiling(
    options: Options,
    selection: Sessions.Selection = Sessions.Selection.empty,
    progress: Progress = new Progress,
    dirs: List[Path] = Nil,
    select_dirs: List[Path] = Nil,
    numa_shuffling: Boolean = false,
    max_jobs: Int = 1,
    anonymous_theories: Boolean = false
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
      build_heap: Boolean = false,
      clean_build: Boolean = false
    ): Build.Results = {
      val results =
        Build.build(options, progress = progress,
          selection = selection, build_heap = build_heap, clean_build = clean_build,
          dirs = sessions_dirs, numa_shuffling = numa_shuffling, max_jobs = max_jobs)

      if (results.ok) results else error("Build failed")
    }


    /* session builds and profiling */

    progress.echo("Build session requirements:")
    build(sessions_selection.copy(requirements = true), build_heap = true)
    progress.echo("DONE")

    progress.echo("Build sessions:")
    val build_results = build(sessions_selection, build_heap = true, clean_build = true)
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
            parent = parent,
            anonymous_theories = anonymous_theories)
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
        var max_jobs = 1
        var anonymous_theories = false
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
    -n           anonymous theories: suppress details of private projects
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
          "j:" -> (arg => max_jobs = Value.Int.parse(arg)),
          "n" -> (_ => anonymous_theories = true),
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
              max_jobs = max_jobs,
              anonymous_theories = anonymous_theories)
          }

        results.output(output_dir = output_dir.absolute, progress = progress)
      })
}
