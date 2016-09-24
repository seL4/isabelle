object stats extends isabelle.Isabelle_Tool.Body {

  import isabelle._

  val target_dir = Path.explode("stats")
  val jobs = List("isabelle-nightly-benchmark", "isabelle-nightly-slow")

  val html_header = """<!DOCTYPE HTML PUBLIC "-//IETF//DTD HTML//EN">
<html>
<head><title>Performance statistics from session build output</title></head>
<body>
"""

  val html_footer = """
</body>
</html>
"""

  def generate(job: String): Unit = {
    println(s"=== $job ===")

    val dir = target_dir + Path.basic(job)
    val sessions = Build_Stats.present_job(job, dir)

    val sections =
      cat_lines(
        sessions.map(session =>
          "<p id=" + quote("session_" + HTML.output(session)) + ">" +
          "<h2>" + HTML.output(session) + "</h2>" +
          "<img src=" + quote(HTML.output(session + ".png")) + "></p>\n"))

    val toc =
      cat_lines(
        sessions.map(session =>
          "<li><a href=" + quote("#session_" + HTML.output(session)) + ">" +
          HTML.output(session) + "</a></li>\n"))

    val html =
      html_header + "\n<h1>" + HTML.output(job) + "</h1>\n" + "<div><ul>" + toc + "</ul></div>\n" +
      sections + html_footer

    File.write(dir + Path.basic("index.html"), html)
  }

  override final def apply(args: List[String]): Unit = {
    jobs.foreach(generate)

    File.write(target_dir + Path.basic("index.html"),
      html_header + "\n<ul>\n" +
      cat_lines(
        jobs.map(job => """<li> <a href=""" + quote(HTML.output(job + "/index.html")) + """>""" +
          HTML.output(job) + """</a> </li>""")) +
      "\n</ul>\n" + html_footer)
  }

}
