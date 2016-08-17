/*  Title:      Pure/Tools/build_stats.scala
    Author:     Makarius

Statistics from session build output.
*/

package isabelle


import scala.collection.mutable
import scala.util.matching.Regex


object Build_Stats
{
  /* parse build output */

  private val Session_Finished1 =
    new Regex("""^Finished (\S+) \((\d+):(\d+):(\d+) elapsed time, (\d+):(\d+):(\d+) cpu time.*$""")
  private val Session_Finished2 =
    new Regex("""^Finished (\S+) \((\d+):(\d+):(\d+) elapsed time.*$""")
  private val Session_Timing =
    new Regex("""^Timing (\S+) \((\d) threads, (\d+\.\d+)s elapsed time, (\d+\.\d+)s cpu time, (\d+\.\d+)s GC time.*$""")

  private object ML_Option
  {
    def unapply(s: String): Option[(String, String)] =
      s.indexOf('=') match {
        case -1 => None
        case i =>
          val a = s.substring(0, i)
          Library.try_unquote(s.substring(i + 1)) match {
            case Some(b) if Build.ml_options.contains(a) => Some((a, b))
            case _ => None
          }
      }
  }

  def parse(text: String): Build_Stats =
  {
    import Properties.Value

    val ml_options = new mutable.ListBuffer[(String, String)]
    var finished = Map.empty[String, Timing]
    var timing = Map.empty[String, Timing]
    var threads = Map.empty[String, Int]

    for (line <- split_lines(text)) {
      line match {
        case Session_Finished1(name,
            Value.Int(e1), Value.Int(e2), Value.Int(e3),
            Value.Int(c1), Value.Int(c2), Value.Int(c3)) =>
          val elapsed = Time.hms(e1, e2, e3)
          val cpu = Time.hms(c1, c2, c3)
          finished += (name -> Timing(elapsed, cpu, Time.zero))
        case Session_Finished2(name,
            Value.Int(e1), Value.Int(e2), Value.Int(e3)) =>
          val elapsed = Time.hms(e1, e2, e3)
          finished += (name -> Timing(elapsed, Time.zero, Time.zero))
        case Session_Timing(name,
            Value.Int(t), Value.Double(e), Value.Double(c), Value.Double(g)) =>
          val elapsed = Time.seconds(e)
          val cpu = Time.seconds(c)
          val gc = Time.seconds(g)
          timing += (name -> Timing(elapsed, cpu, gc))
          threads += (name -> t)
        case ML_Option(option) => ml_options += option
        case _ =>
      }
    }

    Build_Stats(ml_options.toList, finished, timing, threads)
  }


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
    val build_infos = CI_API.build_job_builds(job).sortBy(_.timestamp).reverse.take(history_length)
    if (build_infos.isEmpty) error("No build infos for job " + quote(job))

    val all_build_stats =
      Par_List.map((info: CI_API.Build_Info) =>
        (info.timestamp / 1000, parse(Url.read(info.output))), build_infos)
    val all_sessions =
      (Set.empty[String] /: all_build_stats)(
        { case (s, (_, stats)) => s ++ stats.sessions })

    def check_threshold(stats: Build_Stats, session: String): Boolean =
      stats.finished.get(session) match {
        case Some(t) => t.elapsed >= elapsed_threshold
        case None => false
      }

    val sessions =
      for {
        session <- (if (only_sessions.isEmpty) all_sessions else all_sessions & only_sessions)
        if all_build_stats.filter({ case (_, stats) => check_threshold(stats, session) }).length >= 3
      } yield session

    Isabelle_System.mkdirs(dir)
    for (session <- sessions) {
      Isabelle_System.with_tmp_file(session, "png") { data_file =>
        Isabelle_System.with_tmp_file(session, "gnuplot") { plot_file =>
          val data =
            for { (t, stats) <- all_build_stats if stats.finished.isDefinedAt(session) }
            yield {
              val finished = stats.finished.getOrElse(session, Timing.zero)
              val timing = stats.timing.getOrElse(session, Timing.zero)
              List(t.toString, finished.elapsed.minutes, finished.cpu.minutes,
                timing.elapsed.minutes, timing.cpu.minutes, timing.gc.minutes).mkString(" ")
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

          val data_file_name = File.standard_path(data_file.getAbsolutePath)
          File.write(plot_file, """
set terminal png size """ + size._1 + "," + size._2 + """
set output """ + quote(File.standard_path(dir + Path.basic(session + ".png"))) + """
set xdata time
set timefmt "%s"
set format x "%d-%b"
set xlabel """ + quote(session) + """ noenhanced
set key left top
plot [] [0:] """ + plots.map(s => quote(data_file_name) + " " + s).mkString(", ") + "\n")
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


  /* Isabelle tool wrapper */

  private val html_header = """<!DOCTYPE HTML PUBLIC "-//IETF//DTD HTML//EN">
<html>
<head><title>Performance statistics from session build output</title></head>
<body>
"""
  private val html_footer = """
</body>
</html>
"""

  val isabelle_tool =
    Isabelle_Tool("build_stats", "present statistics from session build output", args =>
    {
      var target_dir = Path.explode("stats")
      var ml_timing = default_ml_timing
      var only_sessions = default_only_sessions
      var elapsed_threshold = default_elapsed_threshold
      var history_length = default_history_length
      var size = default_size

      val getopts = Getopts("""
Usage: isabelle build_stats [OPTIONS] [JOBS ...]

  Options are:
    -D DIR       target directory (default "stats")
    -M           only ML timing
    -S SESSIONS  only given SESSIONS (comma separated)
    -T THRESHOLD only sessions with elapsed time >= THRESHOLD (minutes)
    -l LENGTH    length of history (default 100)
    -m           include ML timing
    -s WxH       size of PNG image (default 800x600)

  Present statistics from session build output of the given JOBS, from Jenkins
  continuous build service specified as URL via ISABELLE_JENKINS_ROOT.
""",
        "D:" -> (arg => target_dir = Path.explode(arg)),
        "M" -> (_ => ml_timing = Some(true)),
        "S:" -> (arg => only_sessions = space_explode(',', arg).toSet),
        "T:" -> (arg => elapsed_threshold = Time.minutes(Properties.Value.Double.parse(arg))),
        "l:" -> (arg => history_length = Properties.Value.Int.parse(arg)),
        "m" -> (_ => ml_timing = Some(false)),
        "s:" -> (arg =>
          space_explode('x', arg).map(Properties.Value.Int.parse(_)) match {
            case List(w, h) if w > 0 && h > 0 => size = (w, h)
            case _ => error("Error bad PNG image size: " + quote(arg))
          }))

      val jobs = getopts(args)
      val all_jobs = CI_API.build_jobs()
      val bad_jobs = jobs.filterNot(all_jobs.contains(_)).sorted

      if (jobs.isEmpty)
        error("No build jobs given. Available jobs: " + commas(all_jobs))

      if (bad_jobs.nonEmpty)
        error("Unknown build jobs: " + commas(bad_jobs) +
          "\nAvailable jobs: " + commas(all_jobs.sorted))

      for (job <- jobs) {
        val dir = target_dir + Path.basic(job)
        Output.writeln(dir.implode)
        val sessions =
          present_job(job, dir, history_length, size, only_sessions, elapsed_threshold, ml_timing)
        File.write(dir + Path.basic("index.html"),
          html_header + "\n<h1>" + HTML.output(job) + "</h1>\n" +
          cat_lines(
            sessions.map(session =>
              """<br/><img src=""" + quote(HTML.output(session + ".png")) + """><br/>""")) +
          "\n" + html_footer)
      }

      File.write(target_dir + Path.basic("index.html"),
        html_header + "\n<ul>\n" +
        cat_lines(
          jobs.map(job => """<li> <a href=""" + quote(HTML.output(job + "/index.html")) + """>""" +
            HTML.output(job) + """</a> </li>""")) +
        "\n</ul>\n" + html_footer)
  })
}

sealed case class Build_Stats(
  ml_options: List[(String, String)],
  finished: Map[String, Timing],
  timing: Map[String, Timing],
  threads: Map[String, Int])
{
  val sessions: Set[String] = finished.keySet ++ timing.keySet

  override def toString: String =
    sessions.toList.sorted.mkString("Build_Stats(", ", ", ")")
}
