/*  Title:      Pure/Build/build_profiling.scala
    Author:     Makarius

Build sessions with presentation of profiling results.
*/

package isabelle


import scala.collection.mutable


object Build_Profiling {
  /* presentation */

  def default_image_width: Int = 800
  def default_image_height: Int = 600

  def image_name(name: String, kind: String, ext: String = "png"): String =
    name + "_" + kind + "." + ext

  sealed case class Image(name: String, width: Int, height: Int) {
    def path: Path = Path.basic(name)

    def write_gnuplot_png(
      dir: Path,
      data: Path,
      title: String,
      plots: List[String],
      range: String
    ): Image = {
      Isabelle_System.with_tmp_file("gnuplot") { tmp_file =>
        File.write(tmp_file, """
set terminal png size """ + width + "," + height + """
set output """ + quote(File.standard_path(dir + path)) + """
set xdata time
set timefmt "%s"
set format x "%d-%b"
set xlabel """ + quote(title) + """ noenhanced
set key left bottom
plot [] """ + range + " " +
          plots.map(s => quote(File.standard_path(data)) + " " + s).mkString(", ") + "\n")

        val result = Isabelle_System.bash("\"$ISABELLE_GNUPLOT\" " + File.bash_path(tmp_file))
        if (!result.ok) result.error("Gnuplot failed for " + quote(title)).check
      }
      this
    }

    def write_chart_png(dir: Path, ml_stats: ML_Statistics, fields: ML_Statistics.Fields): Image = {
      val chart = ml_stats.chart(fields.title + ": " + ml_stats.heading, fields.content)
      Graphics_File.write_chart_png((dir + path).file, chart, width, height)
      this
    }
  }

  def html_description_items(
    timing: Timing = Timing.zero,
    ml_timing: Timing = Timing.zero,
    maximum_code: Space = Space.zero,
    average_code: Space = Space.zero,
    maximum_stack: Space = Space.zero,
    average_stack: Space = Space.zero,
    maximum_heap: Space = Space.zero,
    average_heap: Space = Space.zero,
    stored_heap: Space = Space.zero,
    maximum_java_heap: Space = Space.zero,
    average_java_heap: Space = Space.zero,
    isabelle_version: String = "",
    afp_version: String = ""
  ): List[(XML.Body, XML.Body)] = {
    (if (timing.is_zero) Nil
     else List(HTML.text("timing:") -> HTML.text(timing.message_resources))) :::
    (if (ml_timing.is_zero) Nil
     else List(HTML.text("ML timing:") -> HTML.text(ml_timing.message_factor))) :::
    maximum_code.print_relevant.map(s => HTML.text("ML code maximum:") -> HTML.text(s)).toList :::
    average_code.print_relevant.map(s => HTML.text("ML code average:") -> HTML.text(s)).toList :::
    maximum_stack.print_relevant.map(s => HTML.text("ML stack maximum:") -> HTML.text(s)).toList :::
    average_stack.print_relevant.map(s => HTML.text("ML stack average:") -> HTML.text(s)).toList :::
    maximum_heap.print_relevant.map(s => HTML.text("ML heap maximum:") -> HTML.text(s)).toList :::
    average_heap.print_relevant.map(s => HTML.text("ML heap average:") -> HTML.text(s)).toList :::
    stored_heap.print_relevant.map(s => HTML.text("ML heap stored:") -> HTML.text(s)).toList :::
    maximum_java_heap.print_relevant.map(s =>
      HTML.text("Java heap maximum:") -> HTML.text(s)).toList :::
    average_java_heap.print_relevant.map(s =>
      HTML.text("Java heap average:") -> HTML.text(s)).toList :::
    proper_string(isabelle_version).map(s =>
      HTML.text("Isabelle version:") -> HTML.text(s)).toList :::
    proper_string(afp_version).map(s =>
      HTML.text("AFP version:") -> HTML.text(s)).toList
  }


  /* build with profiling results */

  sealed case class Entry(
    session: String,
    session_timing: Build_Log.Session_Timing,
    maximum_java_heap: Space,
    average_java_heap: Space,
    maximum_java_heap_major: Space,
    average_java_heap_major: Space,
    maximum_heap: Space,
    average_heap: Space,
    stored_heap: Space,
    isabelle_version: String,
    afp_version: String,
    images: List[Image]
  ) {
    def order: Long = - session_timing.process_timing.elapsed.ms
  }

  sealed case class Results(build_results: Build.Results, entries: List[Entry]) {
    def rc: Int = build_results.rc
  }

  val default_output_dir: Path = Path.explode("output")

  def build_profiling(
    options: Options,
    title: String = "",
    output_dir: Path = default_output_dir,
    selection: Sessions.Selection = Sessions.Selection.empty,
    progress: Progress = new Progress,
    build_heap: Boolean = false,
    clean_build: Boolean = false,
    afp_root: Option[Path] = None,
    dirs: List[Path] = Nil,
    select_dirs: List[Path] = Nil,
    numa_shuffling: Boolean = false,
    max_jobs: Int = 1,
    fresh_build: Boolean = false,
    image_width: Int = default_image_width,
    image_height: Int = default_image_height
  ): Results = {
    val results =
      Build.build(options, selection = selection, progress = progress, build_heap = build_heap,
        clean_build = clean_build, afp_root = afp_root, dirs = dirs, select_dirs = select_dirs,
        numa_shuffling = numa_shuffling, max_jobs = Some(max_jobs), fresh_build = fresh_build)

    progress.echo("Output directory " + output_dir.absolute)
    Isabelle_System.make_directory(output_dir)

    val isabelle_version = Mercurial.id_repository(Path.ISABELLE_HOME).getOrElse("")
    val afp_version = afp_root.flatMap(Mercurial.id_repository(_)).getOrElse("")

    val store = results.store
    val raw_entries =
      for (session <- results.sessions_ok) yield {
        using(store.open_database(session)) { db =>
          val session_timing = store.read_session_timing(db, session)
          val ml_stats = ML_Statistics(store.read_ml_statistics(db, session))

          def chart_image(kind: String, fields: ML_Statistics.Fields): Image =
            Image(image_name(session, kind), image_width, image_height)
              .write_chart_png(output_dir, ml_stats, fields)

          val images =
            List(
              chart_image("heap", ML_Statistics.heap_fields),
              chart_image("java_heap", ML_Statistics.java_heap_fields)) :::
            (if (session_timing.ml_threads > 1)
              List(
                chart_image("tasks", ML_Statistics.tasks_fields),
                chart_image("workers", ML_Statistics.workers_fields))
             else Nil)

          Entry(
            session = session,
            session_timing = session_timing,
            maximum_java_heap = ml_stats.maximum_java_heap,
            average_java_heap = ml_stats.average_java_heap,
            maximum_java_heap_major = ml_stats.maximum_java_heap_major,
            average_java_heap_major = ml_stats.average_java_heap_major,
            maximum_heap = ml_stats.maximum_heap,
            average_heap = ml_stats.average_heap,
            stored_heap = store.get_session(session).heap_size,
            isabelle_version = isabelle_version,
            afp_version = afp_version,
            images = images)
        }
      }

    val entries = raw_entries.sortBy(_.order)

    val heading = "Build profiling" + if_proper(title, ": " + title)
    HTML.write_document(output_dir, "index.html",
      List(HTML.title(heading)),
      HTML.chapter(heading) ::
      HTML.par(
        List(HTML.itemize(
          entries.map(entry =>
            HTML.link("#session_" + entry.session, HTML.text(entry.session)) ::
            HTML.text(" (" + entry.session_timing.process_timing.message_resources + ")"))))) ::
      entries.flatMap(entry =>
        List(
          HTML.section(HTML.id("session_" + entry.session), entry.session),
          HTML.par(
            HTML.description(
              html_description_items(
                timing = entry.session_timing.process_timing,
                ml_timing = entry.session_timing.ml_timing,
                maximum_heap = entry.maximum_heap,
                average_heap = entry.average_heap,
                stored_heap = entry.stored_heap,
                maximum_java_heap = entry.maximum_java_heap,
                average_java_heap = entry.average_java_heap,
                isabelle_version = entry.isabelle_version,
                afp_version = entry.afp_version)) ::
            entry.images.map(image =>
              HTML.size(image.width / 2, image.height / 2)(HTML.image(image.name)))))))

    Results(results, entries)
  }


  /* Isabelle tool wrapper */

  val isabelle_tool =
    Isabelle_Tool("build_profiling", "build sessions with presentation of profiling results",
      Scala_Project.here, { args =>
        var afp_root: Option[Path] = None
        val base_sessions = new mutable.ListBuffer[String]
        val select_dirs = new mutable.ListBuffer[Path]
        var numa_shuffling = false
        var output_dir = default_output_dir
        var requirements = false
        var title = ""
        val exclude_session_groups = new mutable.ListBuffer[String]
        var all_sessions = false
        var build_heap = false
        var clean_build = false
        val dirs = new mutable.ListBuffer[Path]
        var fresh_build = false
        val session_groups = new mutable.ListBuffer[String]
        var max_jobs = 1
        var options = Options.init(specs = Options.Spec.ISABELLE_BUILD_OPTIONS)
        var verbose = false
        val exclude_sessions = new mutable.ListBuffer[String]

        val getopts = Getopts("""
Usage: isabelle build_profiling [OPTIONS] [SESSIONS ...]

  Options are:
    -A ROOT      include AFP with given root directory (":" for """ + AFP.BASE.implode + """)
    -B NAME      include session NAME and all descendants
    -D DIR       include session directory and select its sessions
    -N           cyclic shuffling of NUMA CPU nodes (performance tuning)
    -O DIR       output directory (default: """ + default_output_dir + """)
    -R           refer to requirements of selected sessions
    -T TEXT      title for presentation
    -X NAME      exclude sessions from group NAME and all descendants
    -a           select all sessions
    -b           build heap images
    -c           clean build
    -d DIR       include session directory
    -f           fresh build
    -g NAME      select session group NAME
    -j INT       maximum number of parallel jobs (default 1)
    -o OPTION    override Isabelle system OPTION (via NAME=VAL or NAME)
    -v           verbose
    -x NAME      exclude session NAME and all descendants

  Build sessions with presentation of profiling results.""",
          "A:" -> (arg => afp_root = Some(if (arg == ":") AFP.BASE else Path.explode(arg))),
          "B:" -> (arg => base_sessions += arg),
          "D:" -> (arg => select_dirs += Path.explode(arg)),
          "N" -> (_ => numa_shuffling = true),
          "O:" -> (arg => output_dir = Path.explode(arg)),
          "R" -> (_ => requirements = true),
          "T:" -> (arg => title = arg),
          "X:" -> (arg => exclude_session_groups += arg),
          "a" -> (_ => all_sessions = true),
          "b" -> (_ => build_heap = true),
          "c" -> (_ => clean_build = true),
          "d:" -> (arg => dirs += Path.explode(arg)),
          "f" -> (_ => fresh_build = true),
          "g:" -> (arg => session_groups += arg),
          "j:" -> (arg => max_jobs = Value.Int.parse(arg)),
          "o:" -> (arg => options = options + arg),
          "v" -> (_ => verbose = true),
          "x:" -> (arg => exclude_sessions += arg))

        val sessions = getopts(args)

        val progress = new Console_Progress(verbose = verbose)

        progress.echo("Started at " + Build_Log.print_date(progress.start) + "\n")

        val results =
          progress.interrupt_handler {
            build_profiling(options,
              title = title,
              output_dir = output_dir,
              selection = Sessions.Selection(
                requirements = requirements,
                all_sessions = all_sessions,
                base_sessions = base_sessions.toList,
                exclude_session_groups = exclude_session_groups.toList,
                exclude_sessions = exclude_sessions.toList,
                session_groups = session_groups.toList,
                sessions = sessions),
              progress = progress,
              build_heap = build_heap,
              clean_build = clean_build,
              afp_root = afp_root,
              dirs = dirs.toList,
              select_dirs = select_dirs.toList,
              numa_shuffling = Host.numa_check(progress, numa_shuffling),
              max_jobs = max_jobs,
              fresh_build = fresh_build)
          }

        val stop_date = progress.now()

        progress.echo("\nFinished at " + Build_Log.print_date(stop_date) +
          " (" + (stop_date - progress.start).message_hms + " elapsed time)")

        sys.exit(results.rc)
      })
}
