/*  Title:      Pure/Admin/build_stats_legacy.scala
    Author:     Makarius

Statistics from session build output.
*/

package isabelle


object Build_Stats_Legacy
{
  /* presentation */

  private val default_history_length = 100
  private val default_size = (800, 600)
  private val default_only_sessions = Set.empty[String]
  private val default_elapsed_threshold = Time.zero
  private val default_ml_timing: Option[Boolean] = None

  def present_job(job: String, dir: Path,
    history_length: Int = default_history_length,
    size: (Int, Int) = default_size,
    only_sessions: Set[String] = default_only_sessions,
    elapsed_threshold: Time = default_elapsed_threshold,
    ml_timing: Option[Boolean] = default_ml_timing): List[String] =
  {
    val job_infos = Jenkins.build_job_infos(job).take(history_length)
    if (job_infos.isEmpty) error("No build infos for job " + quote(job))

    val all_infos =
      Par_List.map((info: Jenkins.Job_Info) =>
        {
          val log_file = Build_Log.Log_File(info.log_filename.implode, Url.read(info.main_log))
          (info.date, log_file.parse_build_info())
        }, job_infos)
    val all_sessions =
      (Set.empty[String] /: all_infos)(
        { case (s, (_, info)) => s ++ info.sessions.keySet })

    def check_threshold(info: Build_Log.Build_Info, session: String): Boolean =
    {
      val t = info.timing(session)
      !t.is_zero && t.elapsed >= elapsed_threshold
    }

    val sessions =
      for {
        session <- (if (only_sessions.isEmpty) all_sessions else all_sessions & only_sessions)
        if all_infos.filter({ case (_, info) => check_threshold(info, session) }).length >= 3
      } yield session

    Isabelle_System.mkdirs(dir)
    for (session <- sessions) {
      Isabelle_System.with_tmp_file(session, "png") { data_file =>
        Isabelle_System.with_tmp_file(session, "gnuplot") { plot_file =>
          val data =
            for { (date, info) <- all_infos if info.finished(session) }
            yield {
              val timing1 = info.timing(session)
              val timing2 = info.ml_timing(session)
              List(date.unix_epoch.toString,
                timing1.elapsed.minutes,
                timing1.cpu.minutes,
                timing2.elapsed.minutes,
                timing2.cpu.minutes,
                timing2.gc.minutes).mkString(" ")
            }
          File.write(data_file, cat_lines(data))

          val plots1 =
            List(
              """ using 1:3 smooth sbezier title "cpu time (smooth)" """,
              """ using 1:3 smooth csplines title "cpu time" """,
              """ using 1:2 smooth sbezier title "elapsed time (smooth)" """,
              """ using 1:2 smooth csplines title "elapsed time" """)
          val plots2 =
            List(
              """ using 1:5 smooth sbezier title "ML cpu time (smooth)" """,
              """ using 1:5 smooth csplines title "ML cpu time" """,
              """ using 1:4 smooth sbezier title "ML elapsed time (smooth)" """,
              """ using 1:4 smooth csplines title "ML elapsed time" """,
              """ using 1:6 smooth sbezier title "ML gc time (smooth)" """,
              """ using 1:6 smooth csplines title "ML gc time" """)
          val plots =
            ml_timing match {
              case None => plots1
              case Some(false) => plots1 ::: plots2
              case Some(true) => plots2
            }

          File.write(plot_file, """
set terminal png size """ + size._1 + "," + size._2 + """
set output """ + quote(File.standard_path(dir + Path.basic(session + ".png"))) + """
set xdata time
set timefmt "%s"
set format x "%d-%b"
set xlabel """ + quote(session) + """ noenhanced
set key left top
plot [] [0:] """ + plots.map(s => quote(data_file.implode) + " " + s).mkString(", ") + "\n")
          val result = Isabelle_System.bash("\"$ISABELLE_GNUPLOT\" " + File.bash_path(plot_file))
          if (result.rc != 0) {
            Output.error_message("Session " + session + ": gnuplot error")
            result.print
          }
        }
      }
    }

    sessions.toList.sorted
  }
}
