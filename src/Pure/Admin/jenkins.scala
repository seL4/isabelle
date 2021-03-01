/*  Title:      Pure/Admin/jenkins.scala
    Author:     Makarius

Support for Jenkins continuous integration service.
*/

package isabelle


import java.net.URL

import scala.util.matching.Regex


object Jenkins
{
  /* server API */

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

  def build_job_names(): List[String] =
    for {
      job <- JSON.array(invoke(root()), "jobs").getOrElse(Nil)
      _class <- JSON.string(job, "_class")
      if _class == "hudson.model.FreeStyleProject"
      name <- JSON.string(job, "name")
    } yield name


  def download_logs(
    options: Options, job_names: List[String], dir: Path, progress: Progress = new Progress): Unit =
  {
    val store = Sessions.store(options)
    val infos = job_names.flatMap(build_job_infos)
    Par_List.map((info: Job_Info) => info.download_log(store, dir, progress), infos)
  }


  /* build log status */

  val build_log_jobs = List("isabelle-nightly-benchmark", "isabelle-nightly-slow")

  val build_status_profiles: List[Build_Status.Profile] =
    build_log_jobs.map(job_name =>
      Build_Status.Profile("jenkins " + job_name,
        sql =
          Build_Log.Prop.build_engine.toString + " = " + SQL.string(Build_Log.Jenkins.engine) +
          " AND " + Build_Log.Data.session_name + " <> " + SQL.string("Pure") + " AND " +
          Build_Log.Data.status + " = " + SQL.string(Build_Log.Session_Status.finished.toString) +
          " AND " + Build_Log.Data.log_name + " LIKE " + SQL.string("%" + job_name)))


  /* job info */

  sealed case class Job_Info(
    job_name: String,
    timestamp: Long,
    main_log: URL,
    session_logs: List[(String, String, URL)])
  {
    val date: Date = Date(Time.ms(timestamp), Date.timezone_berlin)

    def log_filename: Path =
      Build_Log.log_filename(Build_Log.Jenkins.engine, date, List(job_name))

    def read_ml_statistics(store: Sessions.Store, session_name: String): List[Properties.T] =
    {
      def get_log(ext: String): Option[URL] =
        session_logs.collectFirst({ case (a, b, url) if a == session_name && b == ext => url })

      get_log("db") match {
        case Some(url) =>
          Isabelle_System.with_tmp_file(session_name, "db") { database =>
            Bytes.write(database, Bytes.read(url))
            using(SQLite.open_database(database))(db => store.read_ml_statistics(db, session_name))
          }
        case None =>
          get_log("gz") match {
            case Some(url) =>
              val log_file = Build_Log.Log_File(session_name, Url.read_gzip(url))
              log_file.parse_session_info(ml_statistics = true).ml_statistics
            case None => Nil
          }
      }
    }

    def download_log(store: Sessions.Store, dir: Path, progress: Progress = new Progress): Unit =
    {
      val log_dir = dir + Build_Log.log_subdir(date)
      val log_path = log_dir + log_filename.xz

      if (!log_path.is_file) {
        progress.echo(log_path.expand.implode)
        Isabelle_System.make_directory(log_dir)

        val ml_statistics =
          session_logs.map(_._1).distinct.sorted.flatMap(session_name =>
            read_ml_statistics(store, session_name).
              map(props => (Build_Log.SESSION_NAME -> session_name) :: props))

        File.write_xz(log_path,
          terminate_lines(Url.read(main_log) ::
            ml_statistics.map(Protocol.ML_Statistics_Marker.apply)),
          XZ.options(6))
      }
    }
  }

  def build_job_infos(job_name: String): List[Job_Info] =
  {
    val Session_Log = new Regex("""^.*/log/([^/]+)\.(db|gz)$""")

    val infos =
      for {
        build <-
          JSON.array(
            invoke(root() + "/job/" + job_name, "tree=allBuilds[number,timestamp,artifacts[*]]"),
            "allBuilds").getOrElse(Nil)
        number <- JSON.int(build, "number")
        timestamp <- JSON.long(build, "timestamp")
      } yield {
        val job_prefix = root() + "/job/" + job_name + "/" + number
        val main_log = Url(job_prefix + "/consoleText")
        val session_logs =
          for {
            artifact <- JSON.array(build, "artifacts").getOrElse(Nil)
            log_path <- JSON.string(artifact, "relativePath")
            (name, ext) <- (log_path match { case Session_Log(a, b) => Some((a, b)) case _ => None })
          } yield (name, ext, Url(job_prefix + "/artifact/" + log_path))
        Job_Info(job_name, timestamp, main_log, session_logs)
      }

    infos.sortBy(info => - info.timestamp)
  }
}
