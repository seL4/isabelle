/*  Title:      Pure/Admin/build_status.scala
    Author:     Makarius

Present recent build status information from database.
*/

package isabelle


object Build_Status {
  /* defaults */

  val default_target_dir = Path.explode("build_status")
  val default_image_size = (800, 600)
  val default_history = 30

  def default_profiles: List[Profile] = Isabelle_Cronjob.build_status_profiles


  /* data profiles */

  sealed case class Profile(
    description: String,
    history: Int = 0,
    afp: Boolean = false,
    bulky: Boolean = false,
    sql: String = ""
  ) {
    def days(options: Options): Int = options.int("build_log_history") max history

    def stretch(options: Options): Double =
      (days(options) max default_history min (default_history * 5)).toDouble / default_history

    def select(
      options: Options,
      ml_statistics: Boolean = false,
      only_sessions: Set[String] = Set.empty
    ): PostgreSQL.Source = {
      val columns =
        List(
          Build_Log.Column.pull_date(afp = false),
          Build_Log.Column.pull_date(afp = true),
          Build_Log.Prop.build_start,
          Build_Log.Prop.build_host,
          Build_Log.Prop.isabelle_version,
          Build_Log.Prop.afp_version,
          Build_Log.Settings.ISABELLE_BUILD_OPTIONS,
          Build_Log.Settings.ML_PLATFORM,
          Build_Log.Column.log_name,
          Build_Log.Column.session_name,
          Build_Log.Column.chapter,
          Build_Log.Column.groups,
          Build_Log.Column.threads,
          Build_Log.Column.timing_elapsed,
          Build_Log.Column.timing_cpu,
          Build_Log.Column.timing_gc,
          Build_Log.Column.ml_timing_elapsed,
          Build_Log.Column.ml_timing_cpu,
          Build_Log.Column.ml_timing_gc,
          Build_Log.Column.heap_size,
          Build_Log.Column.status,
          Build_Log.Column.errors) :::
        (if (ml_statistics) List(Build_Log.Column.ml_statistics) else Nil)

      Build_Log.private_data.universal_table.select(columns, distinct = true, sql =
        SQL.where_and(
          Build_Log.private_data.recent(Build_Log.Column.pull_date(afp), days(options)),
          Build_Log.Column.status.member(
            List(
              Build_Log.Session_Status.finished.toString,
              Build_Log.Session_Status.failed.toString)),
          if_proper(only_sessions, Build_Log.Column.session_name.member(only_sessions)),
          if_proper(sql, SQL.enclose(sql))))
    }
  }


  /* build status */

  def build_status(options: Options,
    progress: Progress = new Progress,
    profiles: List[Profile] = default_profiles,
    only_sessions: Set[String] = Set.empty,
    target_dir: Path = default_target_dir,
    ml_statistics: Boolean = false,
    image_size: (Int, Int) = default_image_size
  ): Unit = {
    val ml_statistics_domain =
      Iterator(ML_Statistics.heap_fields, ML_Statistics.program_fields, ML_Statistics.tasks_fields,
        ML_Statistics.workers_fields).flatMap(_._2).toSet

    val data =
      read_data(options, progress = progress, profiles = profiles, only_sessions = only_sessions,
        ml_statistics = ml_statistics, ml_statistics_domain = ml_statistics_domain)

    present_data(data, progress = progress, target_dir = target_dir, image_size = image_size)
  }


  /* read data */

  sealed case class Data(date: Date, entries: List[Data_Entry])
  sealed case class Data_Entry(
    name: String,
    hosts: List[String],
    stretch: Double,
    sessions: List[Session]
  ) {
    def failed_sessions: List[Session] =
      sessions.filter(_.head.failed).sortBy(_.name)
  }
  sealed case class Session(
    name: String,
    threads: Int,
    entries: Map[String, Entry],
    ml_statistics: ML_Statistics,
    ml_statistics_date: Long
  ) {
    require(entries.nonEmpty, "no entries")

    lazy val sorted_entries: List[Entry] =
      entries.valuesIterator.toList.sortBy(entry => - entry.date)

    def head: Entry = sorted_entries.head
    def order: Long = - head.timing.elapsed.ms

    def finished_entries: List[Entry] = sorted_entries.filter(_.finished)
    def finished_entries_size: Int = finished_entries.map(_.date).toSet.size

    def check_timing: Boolean = finished_entries_size >= 3
    def check_heap: Boolean =
      finished_entries_size >= 3 &&
      finished_entries.forall(entry =>
        entry.maximum_heap.is_proper ||
        entry.average_heap.is_proper ||
        entry.stored_heap.is_proper)

    def make_csv: CSV.File = {
      val header =
        List("session_name",
          "chapter",
          "build_date",
          "pull_date",
          "afp_pull_date",
          "isabelle_version",
          "afp_version",
          "timing_elapsed",
          "timing_cpu",
          "timing_gc",
          "ml_timing_elapsed",
          "ml_timing_cpu",
          "ml_timing_gc",
          "maximum_code",
          "average_code",
          "maximum_stack",
          "average_stack",
          "maximum_heap",
          "average_heap",
          "stored_heap",
          "status")
      val date_format = Date.Format("uuuu-MM-dd HH:mm:ss")
      val records =
        for (entry <- sorted_entries) yield {
          CSV.Record(name,
            entry.chapter,
            date_format(entry.build_start),
            date_format(entry.pull_date),
            entry.afp_pull_date match { case Some(date) => date_format(date) case None => "" },
            entry.isabelle_version,
            entry.afp_version,
            entry.timing.elapsed.ms,
            entry.timing.cpu.ms,
            entry.timing.gc.ms,
            entry.ml_timing.elapsed.ms,
            entry.ml_timing.cpu.ms,
            entry.ml_timing.gc.ms,
            entry.maximum_code,
            entry.average_code,
            entry.maximum_stack,
            entry.average_stack,
            entry.maximum_heap,
            entry.average_heap,
            entry.stored_heap,
            entry.status)
        }
      CSV.File(name, header, records)
    }
  }
  sealed case class Entry(
    chapter: String,
    build_start: Date,
    pull_date: Date,
    afp_pull_date: Option[Date],
    isabelle_version: String,
    afp_version: String,
    timing: Timing,
    ml_timing: Timing,
    maximum_code: Space,
    average_code: Space,
    maximum_stack: Space,
    average_stack: Space,
    maximum_heap: Space,
    average_heap: Space,
    stored_heap: Space,
    status: Build_Log.Session_Status,
    errors: List[String]
  ) {
    val date: Long = (afp_pull_date getOrElse pull_date).unix_epoch

    def finished: Boolean = status == Build_Log.Session_Status.finished
    def failed: Boolean = status == Build_Log.Session_Status.failed

    def present_errors(name: String): XML.Body = {
      if (errors.isEmpty)
        HTML.text(name + print_version(isabelle_version, afp_version, chapter))
      else {
        HTML.tooltip_errors(HTML.text(name), errors.map(s => HTML.text(Symbol.decode(s)))) ::
          HTML.text(print_version(isabelle_version, afp_version, chapter))
      }
    }
  }

  sealed case class Image(name: String, width: Int, height: Int) {
    def path: Path = Path.basic(name)
  }

  def print_version(
    isabelle_version: String,
    afp_version: String = "",
    chapter: String = AFP.chapter
  ): String = {
    val body =
      proper_string(isabelle_version).map("Isabelle/" + _).toList :::
      (if (chapter == AFP.chapter) proper_string(afp_version).map("AFP/" + _) else None).toList
    if_proper(body, body.mkString(" (", ", ", ")"))
  }

  def read_data(options: Options,
    progress: Progress = new Progress,
    profiles: List[Profile] = default_profiles,
    only_sessions: Set[String] = Set.empty,
    ml_statistics: Boolean = false,
    ml_statistics_domain: String => Boolean = _ => true
  ): Data = {
    val date = Date.now()
    var data_hosts = Map.empty[String, Set[String]]
    var data_stretch = Map.empty[String, Double]
    var data_entries = Map.empty[String, Map[String, Session]]

    def get_hosts(data_name: String): Set[String] =
      data_hosts.getOrElse(data_name, Set.empty)

    val store = Build_Log.store(options)

    using(store.open_database()) { db =>
      for (profile <- profiles.sortBy(_.description)) {
        progress.echo("input " + quote(profile.description))

        val afp = profile.afp

        val Threads_Option = """threads\s*=\s*(\d+)""".r

        val sql =
          profile.select(options, ml_statistics = ml_statistics, only_sessions = only_sessions)
        progress.echo(sql, verbose = true)

        db.using_statement(sql) { stmt =>
          using(stmt.execute_query()) { res =>
            while (res.next()) {
              val log_name = res.string(Build_Log.Column.log_name)
              val session_name = res.string(Build_Log.Column.session_name)
              val chapter = res.string(Build_Log.Column.chapter)
              val groups = split_lines(res.string(Build_Log.Column.groups))
              val threads = {
                val threads1 =
                  res.string(Build_Log.Settings.ISABELLE_BUILD_OPTIONS) match {
                    case Threads_Option(Value.Int(i)) => i
                    case _ => 1
                  }
                val threads2 = res.get_int(Build_Log.Column.threads).getOrElse(1)
                threads1 max threads2
              }
              val ml_platform = res.string(Build_Log.Settings.ML_PLATFORM)
              val ml_platform_64 =
                ml_platform.startsWith("x86_64-") || ml_platform.startsWith("arm64-")
              val data_name =
                profile.description +
                  (if (ml_platform_64) ", 64bit" else "") +
                  (if (threads == 1) "" else ", " + threads + " threads")

              res.get_string(Build_Log.Prop.build_host).foreach(host =>
                data_hosts += (data_name -> (get_hosts(data_name) + host)))

              data_stretch += (data_name -> profile.stretch(options))

              val isabelle_version = res.string(Build_Log.Prop.isabelle_version)
              val afp_version = res.string(Build_Log.Prop.afp_version)

              val ml_stats =
                ML_Statistics(
                  if (ml_statistics) {
                    Properties.uncompress(
                      res.bytes(Build_Log.Column.ml_statistics), cache = store.cache)
                  }
                  else Nil,
                  domain = ml_statistics_domain,
                  heading = session_name + print_version(isabelle_version, afp_version, chapter))

              val entry =
                Entry(
                  chapter = chapter,
                  build_start = res.date(Build_Log.Prop.build_start),
                  pull_date = res.date(Build_Log.Column.pull_date(afp = false)),
                  afp_pull_date =
                    if (afp) res.get_date(Build_Log.Column.pull_date(afp = true)) else None,
                  isabelle_version = isabelle_version,
                  afp_version = afp_version,
                  timing =
                    res.timing(
                      Build_Log.Column.timing_elapsed,
                      Build_Log.Column.timing_cpu,
                      Build_Log.Column.timing_gc),
                  ml_timing =
                    res.timing(
                      Build_Log.Column.ml_timing_elapsed,
                      Build_Log.Column.ml_timing_cpu,
                      Build_Log.Column.ml_timing_gc),
                  maximum_code = Space.B(ml_stats.maximum(ML_Statistics.CODE_SIZE)),
                  average_code = Space.B(ml_stats.average(ML_Statistics.CODE_SIZE)),
                  maximum_stack = Space.B(ml_stats.maximum(ML_Statistics.STACK_SIZE)),
                  average_stack = Space.B(ml_stats.average(ML_Statistics.STACK_SIZE)),
                  maximum_heap = Space.B(ml_stats.maximum(ML_Statistics.HEAP_SIZE)),
                  average_heap = Space.B(ml_stats.average(ML_Statistics.HEAP_SIZE)),
                  stored_heap = Space.bytes(res.long(Build_Log.Column.heap_size)),
                  status = Build_Log.Session_Status.valueOf(res.string(Build_Log.Column.status)),
                  errors =
                    Build_Log.uncompress_errors(
                      res.bytes(Build_Log.Column.errors), cache = store.cache))

              val sessions = data_entries.getOrElse(data_name, Map.empty)
              val session =
                sessions.get(session_name) match {
                  case None =>
                    val entries = Map(log_name -> entry)
                    Some(Session(session_name, threads, entries, ml_stats, entry.date))
                  case Some(old) if !old.entries.isDefinedAt(log_name) =>
                    val entries1 = old.entries + (log_name -> entry)
                    val (ml_stats1, ml_stats1_date) =
                      if (entry.date > old.ml_statistics_date) (ml_stats, entry.date)
                      else (old.ml_statistics, old.ml_statistics_date)
                    Some(Session(session_name, threads, entries1, ml_stats1, ml_stats1_date))
                  case Some(_) => None
                }

              if (session.isDefined &&
                  (!afp || chapter == AFP.chapter) &&
                  (!profile.bulky || groups.exists(Sessions.bulky_groups))) {
                data_entries += (data_name -> (sessions + (session_name -> session.get)))
              }
            }
          }
        }
      }
    }

    val sorted_entries =
      (for {
        (name, sessions) <- data_entries.toList
        sorted_sessions <- proper_list(sessions.toList.map(_._2).sortBy(_.order))
      }
      yield {
        val hosts = get_hosts(name).toList.sorted
        val stretch = data_stretch(name)
        Data_Entry(name, hosts, stretch, sorted_sessions)
      }).sortBy(_.name)

    Data(date, sorted_entries)
  }


  /* present data */

  def present_data(data: Data,
    progress: Progress = new Progress,
    target_dir: Path = default_target_dir,
    image_size: (Int, Int) = default_image_size
  ): Unit = {
    def clean_name(name: String): String =
      name.flatMap(c => if (c == ' ' || c == '/') "_" else if (c == ',') "" else c.toString)

    HTML.write_document(target_dir, "index.html",
      List(HTML.title("Isabelle build status")),
      List(HTML.chapter("Isabelle build status"),
        HTML.par(
          List(HTML.description(
            List(HTML.text("status date:") -> HTML.text(data.date.toString))))),
        HTML.par(
          List(HTML.itemize(data.entries.map(data_entry =>
            List(
              HTML.link(clean_name(data_entry.name) + "/index.html",
                HTML.text(data_entry.name))) :::
            (data_entry.failed_sessions match {
              case Nil => Nil
              case sessions =>
                HTML.break :::
                List(HTML.span(HTML.error_message, HTML.text("Failed sessions:"))) :::
                List(HTML.itemize(sessions.map(s => s.head.present_errors(s.name))))
            })
          ))))))

    for (data_entry <- data.entries) {
      val data_name = data_entry.name

      val (image_width, image_height) = image_size
      val image_width_stretch = (image_width * data_entry.stretch).toInt

      progress.echo("output " + quote(data_name))

      val dir = Isabelle_System.make_directory(target_dir + Path.basic(clean_name(data_name)))

      val data_files =
        (for (session <- data_entry.sessions) yield {
          val csv_file = session.make_csv
          csv_file.write(dir)
          session.name -> csv_file
        }).toMap

      val session_plots =
        Par_List.map((session: Session) =>
          Isabelle_System.with_tmp_file(session.name, "data") { data_file =>
            Isabelle_System.with_tmp_file(session.name, "gnuplot") { gnuplot_file =>

              def plot_name(kind: String): String = session.name + "_" + kind + ".png"

              File.write(data_file,
                cat_lines(
                  session.finished_entries.map(entry =>
                    List(entry.date.toString,
                      entry.timing.elapsed.minutes.toString,
                      entry.timing.resources.minutes.toString,
                      entry.ml_timing.elapsed.minutes.toString,
                      entry.ml_timing.resources.minutes.toString,
                      entry.maximum_code.MiB.toString,
                      entry.average_code.MiB.toString,
                      entry.maximum_stack.MiB.toString,
                      entry.average_stack.MiB.toString,
                      entry.maximum_heap.MiB.toString,
                      entry.average_heap.MiB.toString,
                      entry.stored_heap.MiB.toString).mkString(" "))))

              val max_time =
                (session.finished_entries.foldLeft(0.0) {
                  case (m, entry) =>
                    m.max(entry.timing.elapsed.minutes).
                      max(entry.timing.resources.minutes).
                      max(entry.ml_timing.elapsed.minutes).
                      max(entry.ml_timing.resources.minutes)
                } max 0.1) * 1.1
              val timing_range = "[0:" + max_time + "]"

              def gnuplot(plot_name: String, plots: List[String], range: String): Image = {
                val image = Image(plot_name, image_width_stretch, image_height)

                File.write(gnuplot_file, """
set terminal png size """ + image.width + "," + image.height + """
set output """ + quote(File.standard_path(dir + image.path)) + """
set xdata time
set timefmt "%s"
set format x "%d-%b"
set xlabel """ + quote(session.name) + """ noenhanced
set key left bottom
plot [] """ + range + " " +
                plots.map(s => quote(data_file.implode) + " " + s).mkString(", ") + "\n")

                val result =
                  Isabelle_System.bash("\"$ISABELLE_GNUPLOT\" " + File.bash_path(gnuplot_file))
                if (!result.ok)
                  result.error("Gnuplot failed for " + data_name + "/" + plot_name).check

                image
              }

              val timing_plots = {
                val plots1 =
                  List(
                    """ using 1:2 smooth sbezier title "elapsed time (smooth)" """,
                    """ using 1:2 smooth csplines title "elapsed time" """)
                val plots2 =
                  List(
                    """ using 1:3 smooth sbezier title "cpu time (smooth)" """,
                    """ using 1:3 smooth csplines title "cpu time" """)
                if (session.threads == 1) plots1 else plots1 ::: plots2
              }

              val ml_timing_plots =
                List(
                  """ using 1:4 smooth sbezier title "ML elapsed time (smooth)" """,
                  """ using 1:4 smooth csplines title "ML elapsed time" """,
                  """ using 1:5 smooth sbezier title "ML cpu time (smooth)" """,
                  """ using 1:5 smooth csplines title "ML cpu time" """)

              val heap_plots =
                List(
                  """ using 1:10 smooth sbezier title "heap maximum (smooth)" """,
                  """ using 1:10 smooth csplines title "heap maximum" """,
                  """ using 1:11 smooth sbezier title "heap average (smooth)" """,
                  """ using 1:11 smooth csplines title "heap average" """,
                  """ using 1:12 smooth sbezier title "heap stored (smooth)" """,
                  """ using 1:12 smooth csplines title "heap stored" """)

              def jfreechart(plot_name: String, fields: ML_Statistics.Fields): Image = {
                val image = Image(plot_name, image_width, image_height)
                val chart =
                  session.ml_statistics.chart(
                    fields.title + ": " + session.ml_statistics.heading, fields.names)
                Graphics_File.write_chart_png(
                  (dir + image.path).file, chart, image.width, image.height)
                image
              }

              val images =
                (if (session.check_timing)
                  List(
                    gnuplot(plot_name("timing"), timing_plots, timing_range),
                    gnuplot(plot_name("ml_timing"), ml_timing_plots, timing_range))
                 else Nil) :::
                (if (session.check_heap)
                  List(gnuplot(plot_name("heap"), heap_plots, "[0:]"))
                 else Nil) :::
                (if (session.ml_statistics.content.nonEmpty)
                  List(jfreechart(plot_name("heap_chart"), ML_Statistics.heap_fields),
                    jfreechart(plot_name("program_chart"), ML_Statistics.program_fields)) :::
                  (if (session.threads > 1)
                    List(
                      jfreechart(plot_name("tasks_chart"), ML_Statistics.tasks_fields),
                      jfreechart(plot_name("workers_chart"), ML_Statistics.workers_fields))
                   else Nil)
                 else Nil)

              session.name -> images
            }
          }, data_entry.sessions).toMap

      HTML.write_document(dir, "index.html",
        List(HTML.title("Isabelle build status for " + data_name)),
        HTML.chapter("Isabelle build status for " + data_name) ::
        HTML.par(
          List(HTML.description(
            List(
              HTML.text("status date:") -> HTML.text(data.date.toString),
              HTML.text("build host:") -> HTML.text(commas(data_entry.hosts)))))) ::
        HTML.par(
          List(HTML.itemize(
            data_entry.sessions.map(session =>
              HTML.link("#session_" + session.name, HTML.text(session.name)) ::
              HTML.text(" (" + session.head.timing.message_resources + ")"))))) ::
        data_entry.sessions.flatMap(session =>
          List(
            HTML.section(HTML.id("session_" + session.name), session.name),
            HTML.par(
              HTML.description(
                List(
                  HTML.text("data:") ->
                    List(HTML.link(data_files(session.name).file_name, HTML.text("CSV"))),
                  HTML.text("timing:") -> HTML.text(session.head.timing.message_resources),
                  HTML.text("ML timing:") -> HTML.text(session.head.ml_timing.message_resources)) :::
                session.head.maximum_code.print_relevant.map(s =>
                  HTML.text("code maximum:") -> HTML.text(s)).toList :::
                session.head.average_code.print_relevant.map(s =>
                  HTML.text("code average:") -> HTML.text(s)).toList :::
                session.head.maximum_stack.print_relevant.map(s =>
                  HTML.text("stack maximum:") -> HTML.text(s)).toList :::
                session.head.average_stack.print_relevant.map(s =>
                  HTML.text("stack average:") -> HTML.text(s)).toList :::
                session.head.maximum_heap.print_relevant.map(s =>
                  HTML.text("heap maximum:") -> HTML.text(s)).toList :::
                session.head.average_heap.print_relevant.map(s =>
                  HTML.text("heap average:") -> HTML.text(s)).toList :::
                session.head.stored_heap.print_relevant.map(s =>
                  HTML.text("heap stored:") -> HTML.text(s)).toList :::
                proper_string(session.head.isabelle_version).map(s =>
                  HTML.text("Isabelle version:") -> HTML.text(s)).toList :::
                proper_string(session.head.afp_version).map(s =>
                  HTML.text("AFP version:") -> HTML.text(s)).toList) ::
              session_plots.getOrElse(session.name, Nil).map(image =>
                HTML.size(image.width / 2, image.height / 2)(HTML.image(image.name)))))))
    }
  }


  /* Isabelle tool wrapper */

  val isabelle_tool =
    Isabelle_Tool("build_status", "present recent build status information from database",
      Scala_Project.here,
      { args =>
        var target_dir = default_target_dir
        var ml_statistics = false
        var only_sessions = Set.empty[String]
        var options = Options.init()
        var image_size = default_image_size
        var verbose = false

        val getopts = Getopts("""
Usage: isabelle build_status [OPTIONS]

  Options are:
    -D DIR       target directory (default """ + default_target_dir + """)
    -M           include full ML statistics
    -S SESSIONS  only given SESSIONS (comma separated)
    -l DAYS      length of relevant history (default """ + options.int("build_log_history") + """)
    -o OPTION    override Isabelle system OPTION (via NAME=VAL or NAME)
    -s WxH       size of PNG image (default """ + image_size._1 + "x" + image_size._2 + """)
    -v           verbose

  Present performance statistics from build log database, which is specified
  via system options build_log_database_host, build_log_database_user,
  build_log_history etc.
""",
          "D:" -> (arg => target_dir = Path.explode(arg)),
          "M" -> (_ => ml_statistics = true),
          "S:" -> (arg => only_sessions = space_explode(',', arg).toSet),
          "l:" -> (arg => options = options + ("build_log_history=" + arg)),
          "o:" -> (arg => options = options + arg),
          "s:" -> (arg =>
            space_explode('x', arg).map(Value.Int.parse) match {
              case List(w, h) if w > 0 && h > 0 => image_size = (w, h)
              case _ => error("Error bad PNG image size: " + quote(arg))
            }),
          "v" -> (_ => verbose = true))

        val more_args = getopts(args)
        if (more_args.nonEmpty) getopts.usage()

        val progress = new Console_Progress(verbose = verbose)

        build_status(options, progress = progress, only_sessions = only_sessions,
          target_dir = target_dir, ml_statistics = ml_statistics, image_size = image_size)
      })
}
