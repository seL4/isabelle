/*  Title:      Pure/Tools/ci_api.scala
    Author:     Makarius

API for Isabelle Jenkins continuous integration services.
*/

package isabelle


import java.net.URL

import scala.util.matching.Regex


object CI_API
{
  /* CI service */

  def root(): String =
    Isabelle_System.getenv_strict("ISABELLE_JENKINS_ROOT")

  def invoke(url: String, args: String*): Any =
  {
    val req = url + "/api/json?" + args.mkString("&")
    val result = Url.read(req)
    try { JSON.parse(result) }
    catch { case ERROR(_) => error("Malformed JSON from " + quote(req)) }
  }


  /* build jobs */

  def build_jobs(): List[String] =
    for {
      job <- JSON.array(invoke(root()), "jobs")
      _class <- JSON.string(job, "_class")
      if _class == "hudson.model.FreeStyleProject"
      name <- JSON.string(job, "name")
    } yield name

  sealed case class Build_Info(
    job_name: String,
    timestamp: Long,
    output: URL,
    session_logs: List[(String, URL)])
  {
    def read_output(): String = Url.read(output)
    def read_log(name: String, full: Boolean): Build.Session_Log_Info =
    {
      val text =
        session_logs.collectFirst({ case (a, b) if a == name => Url.read_gzip(b) }) getOrElse ""
      Build.parse_session_log(name, split_lines(text), full)
    }
  }

  def build_job_builds(job_name: String): List[Build_Info] =
  {
    val Log_Session = new Regex("""^.*/log/([^/]+)\.gz$""")

    for {
      build <- JSON.array(
        invoke(root() + "/job/" + job_name, "tree=builds[number,timestamp,artifacts[*]]"), "builds")
      number <- JSON.int(build, "number")
      timestamp <- JSON.long(build, "timestamp")
    } yield {
      val job_prefix = root() + "/job/" + job_name + "/" + number
      val output = Url(job_prefix + "/consoleText")
      val session_logs =
        for {
          artifact <- JSON.array(build, "artifacts")
          log_path <- JSON.string(artifact, "relativePath")
          session <- (log_path match { case Log_Session(name) => Some(name) case _ => None })
        } yield (session -> Url(job_prefix + "/artifact/" + log_path))
      Build_Info(job_name, timestamp, output, session_logs)
    }
  }
}
