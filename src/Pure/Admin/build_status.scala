/*  Title:      Pure/Admin/build_status.scala
    Author:     Makarius

Present recent build status information from database.
*/

package isabelle


object Build_Status
{
  /* data profiles */

  sealed case class Profile(description: String, sql: String)
  {
    def select(columns: List[SQL.Column], days: Int, only_sessions: Set[String]): SQL.Source =
    {
      val sql_sessions =
        if (only_sessions.isEmpty) ""
        else
          only_sessions.iterator.map(a => Build_Log.Data.session_name + " = " + SQL.string(a))
            .mkString("(", " OR ", ") AND ")

      Build_Log.Data.universal_table.select(columns, distinct = true,
        sql = "WHERE " +
          Build_Log.Data.pull_date + " > " + Build_Log.Data.recent_time(days) + " AND " +
          Build_Log.Data.status + " = " + SQL.string(Build_Log.Session_Status.finished.toString) +
          " AND " + sql_sessions + SQL.enclose(sql) +
          " ORDER BY " + Build_Log.Data.pull_date + " DESC")
    }
  }


  /* build status */

  val default_target_dir = Path.explode("build_status")
  val default_image_size = (800, 600)

  def default_profiles: List[Profile] =
    Jenkins.build_status_profiles ::: Isabelle_Cronjob.build_status_profiles

  def build_status(options: Options,
    progress: Progress = No_Progress,
    profiles: List[Profile] = default_profiles,
    only_sessions: Set[String] = Set.empty,
    verbose: Boolean = false,
    target_dir: Path = default_target_dir,
    image_size: (Int, Int) = default_image_size)
  {
    val data =
      read_data(options, progress = progress, profiles = profiles,
        only_sessions = only_sessions, verbose = verbose)

    present_data(data, progress = progress, target_dir = target_dir, image_size = image_size)
  }


  /* read data */

  sealed case class Data(date: Date, entries: List[Data_Entry])
  sealed case class Data_Entry(name: String, hosts: List[String], sessions: List[Session])
  sealed case class Session(name: String, threads: Int, entries: List[Entry])
  {
    def timing: Timing = if (entries.isEmpty) Timing.zero else entries.head.timing
    def ml_timing: Timing = if (entries.isEmpty) Timing.zero else entries.head.ml_timing
    def order: Long = - timing.elapsed.ms

    def check_timing: Boolean = entries.length >= 3
    def check_heap: Boolean = entries.forall(_.heap_size > 0)
  }
  sealed case class Entry(date: Date, timing: Timing, ml_timing: Timing, heap_size: Long)

  def read_data(options: Options,
    progress: Progress = No_Progress,
    profiles: List[Profile] = default_profiles,
    only_sessions: Set[String] = Set.empty,
    verbose: Boolean = false): Data =
  {
    val date = Date.now()
    var data_hosts = Map.empty[String, Set[String]]
    var data_entries = Map.empty[String, Map[String, Session]]

    def get_hosts(data_name: String): Set[String] =
      data_hosts.getOrElse(data_name, Set.empty)

    val store = Build_Log.store(options)
    using(store.open_database())(db =>
    {
      for (profile <- profiles.sortBy(_.description)) {
        progress.echo("input " + quote(profile.description))
        val columns =
          List(
            Build_Log.Data.pull_date,
            Build_Log.Prop.build_host,
            Build_Log.Settings.ISABELLE_BUILD_OPTIONS,
            Build_Log.Settings.ML_PLATFORM,
            Build_Log.Data.session_name,
            Build_Log.Data.threads,
            Build_Log.Data.timing_elapsed,
            Build_Log.Data.timing_cpu,
            Build_Log.Data.timing_gc,
            Build_Log.Data.ml_timing_elapsed,
            Build_Log.Data.ml_timing_cpu,
            Build_Log.Data.ml_timing_gc,
            Build_Log.Data.heap_size)

        val Threads_Option = """threads\s*=\s*(\d+)""".r

        val sql = profile.select(columns, options.int("build_log_history"), only_sessions)
        if (verbose) progress.echo(sql)

        db.using_statement(sql)(stmt =>
        {
          val res = stmt.execute_query()
          while (res.next()) {
            val session_name = res.string(Build_Log.Data.session_name)
            val threads =
            {
              val threads1 =
                res.string(Build_Log.Settings.ISABELLE_BUILD_OPTIONS) match {
                  case Threads_Option(Value.Int(i)) if session_name == "Pure" => i
                  case _ => 1
                }
              val threads2 = res.get_int(Build_Log.Data.threads).getOrElse(1)
              threads1 max threads2
            }
            val ml_platform = res.string(Build_Log.Settings.ML_PLATFORM)
            val data_name =
              profile.description +
                (if (ml_platform.startsWith("x86_64")) ", 64bit" else "") +
                (if (threads == 1) "" else ", " + threads + " threads")

            val entry =
              Entry(res.date(Build_Log.Data.pull_date),
                res.timing(
                  Build_Log.Data.timing_elapsed,
                  Build_Log.Data.timing_cpu,
                  Build_Log.Data.timing_gc),
                res.timing(
                  Build_Log.Data.ml_timing_elapsed,
                  Build_Log.Data.ml_timing_cpu,
                  Build_Log.Data.ml_timing_gc),
                heap_size = res.long(Build_Log.Data.heap_size))

            res.get_string(Build_Log.Prop.build_host).foreach(host =>
              data_hosts += (data_name -> (get_hosts(data_name) + host)))

            val sessions = data_entries.getOrElse(data_name, Map.empty)
            val entries = sessions.get(session_name).map(_.entries) getOrElse Nil
            val session = Session(session_name, threads, entry :: entries)
            data_entries += (data_name -> (sessions + (session_name -> session)))
          }
        })
      }
    })

    val sorted_entries =
      (for {
        (name, sessions) <- data_entries.toList
        sorted_sessions <-
          proper_list(sessions.toList.map(_._2).filter(_.check_timing).sortBy(_.order))
      } yield Data_Entry(name, get_hosts(name).toList.sorted, sorted_sessions)).sortBy(_.name)

    Data(date, sorted_entries)
  }


  /* present data */

  def present_data(data: Data,
    progress: Progress = No_Progress,
    target_dir: Path = default_target_dir,
    image_size: (Int, Int) = default_image_size)
  {
    def clean_name(name: String): String =
      name.flatMap(c => if (c == ' ' || c == '/') "_" else if (c == ',') "" else c.toString)

    Isabelle_System.mkdirs(target_dir)
    File.write(target_dir + Path.basic("index.html"),
      HTML.output_document(
        List(HTML.title("Isabelle build status")),
        List(HTML.chapter("Isabelle build status"),
          HTML.par(
            List(HTML.itemize(
              List(HTML.bold(HTML.text("status date: ")) :: HTML.text(data.date.toString))))),
          HTML.par(
            List(HTML.itemize(data.entries.map({ case data_entry =>
              List(HTML.link(clean_name(data_entry.name) + "/index.html",
                HTML.text(data_entry.name))) })))))))

    for (data_entry <- data.entries) {
      val data_name = data_entry.name

      progress.echo("output " + quote(data_name))

      val dir = target_dir + Path.basic(clean_name(data_name))
      Isabelle_System.mkdirs(dir)

      val session_plots =
        Par_List.map((session: Session) =>
          Isabelle_System.with_tmp_file(session.name, "data") { data_file =>
            Isabelle_System.with_tmp_file(session.name, "gnuplot") { gnuplot_file =>

              File.write(data_file,
                cat_lines(
                  session.entries.map(entry =>
                    List(entry.date.unix_epoch.toString,
                      entry.timing.elapsed.minutes,
                      entry.timing.resources.minutes,
                      entry.ml_timing.elapsed.minutes,
                      entry.ml_timing.resources.minutes,
                      (entry.heap_size.toDouble / (1024 * 1024)).toString).mkString(" "))))

              val max_time =
                ((0.0 /: session.entries){ case (m, entry) =>
                  m.max(entry.timing.elapsed.minutes).
                    max(entry.timing.resources.minutes).
                    max(entry.ml_timing.elapsed.minutes).
                    max(entry.ml_timing.resources.minutes) } max 0.1) * 1.1
              val timing_range = "[0:" + max_time + "]"

              def gnuplot(plots: List[String], kind: String, range: String): String =
              {
                val plot_name = session.name + "_" + kind + ".png"

                File.write(gnuplot_file, """
set terminal png size """ + image_size._1 + "," + image_size._2 + """
set output """ + quote(File.standard_path(dir + Path.basic(plot_name))) + """
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

                plot_name
              }

              val timing_plots =
              {
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
                  """ using 1:6 smooth sbezier title "heap (smooth)" """,
                  """ using 1:6 smooth csplines title "heap" """)

              val plot_names =
                List(
                  gnuplot(timing_plots, "timing", timing_range),
                  gnuplot(ml_timing_plots, "ml_timing", timing_range)) :::
                (if (session.check_heap) List(gnuplot(heap_plots, "heap", "[0:]")) else Nil)

              session.name -> plot_names
            }
          }, data_entry.sessions).toMap

      File.write(dir + Path.basic("index.html"),
        HTML.output_document(
          List(HTML.title("Isabelle build status for " + data_name)),
          HTML.chapter("Isabelle build status for " + data_name) ::
          HTML.par(
            List(HTML.itemize(
              List(
                HTML.bold(HTML.text("status date: ")) :: HTML.text(data.date.toString),
                HTML.bold(HTML.text("build host: ")) :: HTML.text(commas(data_entry.hosts)))))) ::
          HTML.par(
            List(HTML.itemize(
              data_entry.sessions.map(session =>
                HTML.link("#session_" + session.name, HTML.text(session.name)) ::
                HTML.text(" (" + session.timing.message_resources + ")"))))) ::
          data_entry.sessions.flatMap(session =>
            List(
              HTML.section(session.name) + HTML.id("session_" + session.name),
              HTML.par(
                HTML.itemize(List(
                  HTML.bold(HTML.text("status date: ")) :: HTML.text(data.date.toString),
                  HTML.bold(HTML.text("build host: ")) :: HTML.text(commas(data_entry.hosts)),
                  HTML.bold(HTML.text("timing: ")) :: HTML.text(session.timing.message_resources),
                  HTML.bold(HTML.text("ML timing: ")) ::
                    HTML.text(session.ml_timing.message_resources))) ::
                session_plots.getOrElse(session.name, Nil).map(plot_name =>
                  HTML.image(plot_name) +
                    HTML.width(image_size._1 / 2) +
                    HTML.height(image_size._2 / 2)))))))
    }
  }


  /* Isabelle tool wrapper */

  val isabelle_tool =
    Isabelle_Tool("build_status", "present recent build status information from database", args =>
    {
      var target_dir = default_target_dir
      var only_sessions = Set.empty[String]
      var options = Options.init()
      var image_size = default_image_size
      var verbose = false

      val getopts = Getopts("""
Usage: isabelle build_status [OPTIONS]

  Options are:
    -D DIR       target directory (default """ + default_target_dir + """)
    -S SESSIONS  only given SESSIONS (comma separated)
    -o OPTION    override Isabelle system OPTION (via NAME=VAL or NAME)
    -s WxH       size of PNG image (default """ + image_size._1 + "x" + image_size._2 + """)
    -v           verbose

  Present performance statistics from build log database, which is specified
  via system options build_log_database_host, build_log_database_user,
  build_log_history etc.
""",
        "D:" -> (arg => target_dir = Path.explode(arg)),
        "S:" -> (arg => only_sessions = space_explode(',', arg).toSet),
        "o:" -> (arg => options = options + arg),
        "s:" -> (arg =>
          space_explode('x', arg).map(Value.Int.parse(_)) match {
            case List(w, h) if w > 0 && h > 0 => image_size = (w, h)
            case _ => error("Error bad PNG image size: " + quote(arg))
          }),
        "v" -> (_ => verbose = true))

      val more_args = getopts(args)
      if (more_args.nonEmpty) getopts.usage()

      val progress = new Console_Progress

      build_status(options, progress = progress, only_sessions = only_sessions, verbose = verbose,
        target_dir = target_dir, image_size = image_size)

  }, admin = true)
}
