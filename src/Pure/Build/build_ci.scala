/*  Title:      Pure/Build/build_ci.scala
    Author:     Fabian Huch, TU Munich

Module for automated (continuous integration) builds.
*/

package isabelle


import scala.collection.mutable


object Build_CI {
  def section(title: String): String = "\n=== " + title + " ===\n"


  /* mailing */

  object Mail_System {
    def try_open(options: Options): Option[Mail_System] =
      Exn.capture(new Mail_System(options)) match {
        case Exn.Res(res) if res.server.defined => Some(res)
        case _ => None
      }
  }

  class Mail_System private(options: Options) {
    val from: Mail.Address = Mail.address(options.string("ci_mail_from"))
    val to: Mail.Address = Mail.address(options.string("ci_mail_to"))

    val server: Mail.Server =
      new Mail.Server(Mail.address(options.string("ci_mail_sender")),
        smtp_host = options.string("ci_mail_smtp_host"),
        smtp_port = options.int("ci_mail_smtp_port"),
        user = options.string("ci_mail_user"),
        password = options.string("ci_mail_password"))
  }


  /** ci build jobs **/

  /* hosts */

  sealed trait Hosts {
    def hosts_spec: String
    def max_jobs: Option[Int]
    def prefs: List[Options.Spec]
    def numa_shuffling: Boolean
    def build_cluster: Boolean
  }

  case class Local(host_spec: String, jobs: Int, threads: Int, numa_shuffling: Boolean = true)
    extends Hosts {
    def hosts_spec: String = host_spec
    def max_jobs: Option[Int] = Some(jobs)
    def prefs: List[Options.Spec] = List(Options.Spec.eq("threads", threads.toString))
    def build_cluster: Boolean = false
  }

  case class Cluster(hosts_spec: String, numa_shuffling: Boolean = true) extends Hosts {
    def max_jobs: Option[Int] = None
    def prefs: List[Options.Spec] = Nil
    def build_cluster: Boolean = true
  }


  /* build triggers */

  sealed trait Trigger
  case object On_Commit extends Trigger

  object Timed {
    def nightly(start_time: Time = Time.zero): Timed =
      Timed { (before, now) =>
        val start0 = before.midnight + start_time
        val start1 = now.midnight + start_time
        (before.time < start0.time && start0.time <= now.time) ||
          (before.time < start1.time && start1.time <= now.time)
      }
  }

  case class Timed(in_interval: (Date, Date) => Boolean) extends Trigger


  /* build hooks */

  trait Hook {
    def pre(options: Options, progress: Progress): Unit = ()
    def post(
      options: Options,
      url: Option[Url],
      results: Build.Results,
      progress: Progress
    ): Unit = ()
  }

  object none extends Hook


  /* jobs */

  sealed case class Job(
    name: String,
    description: String,
    hosts: Hosts,
    afp: Boolean = false,
    selection: Sessions.Selection = Sessions.Selection.empty,
    presentation: Boolean = false,
    clean_build: Boolean = false,
    select_dirs: List[Path] = Nil,
    build_prefs: List[Options.Spec] = Nil,
    hook: Hook = none,
    extra_components: List[String] = Nil,
    other_settings: List[String] = Nil,
    trigger: Trigger = On_Commit
  ) {
    override def toString: String = name

    def afp_root: Option[Path] = if (!afp) None else Some(AFP.BASE)

    def prefs: List[Options.Spec] = build_prefs ++ hosts.prefs ++ document_prefs
    def document_prefs: List[Options.Spec] =
      if (!presentation) Nil
      else List(
        Options.Spec.eq("browser_info", "true"),
        Options.Spec.eq("document", "pdf"),
        Options.Spec.eq("document_variants", "document:outline=/proof,/ML"))

    def components: List[String] = (if (!afp) Nil else List("AFP")) ::: extra_components
  }

  private lazy val known_jobs: List[Job] =
    Isabelle_System.make_services(classOf[Isabelle_CI_Jobs]).flatMap(_.jobs)

  def show_jobs: String =
    cat_lines(known_jobs.sortBy(_.name).map(job => job.name + " - " + job.description))

  def the_job(name: String): Job = known_jobs.find(job => job.name == name) getOrElse
    error("Unknown job " + quote(name))


  /* concrete jobs */

  val timing =
    Job("benchmark",
      description = "runs benchmark and timing sessions",
      Local("benchmark", jobs = 1, threads = 6, numa_shuffling = false),
      selection = Sessions.Selection(session_groups = List("timing")),
      clean_build = true,
      select_dirs = List(Path.explode("~~/src/Benchmarks")),
      trigger = Timed.nightly())


  /* build ci */

  def build_ci(
    options: Options,
    job: Job,
    build_hosts: List[Build_Cluster.Host] = Nil,
    url: Option[Url] = None,
    progress: Progress = new Progress
  ): Unit = {
    def return_code(f: => Unit): Int =
      Exn.capture(f) match {
        case Exn.Res(_) => Process_Result.RC.ok
        case Exn.Exn(e) =>
          progress.echo_error_message(e.getMessage)
          Process_Result.RC.error
      }

    val mail_result =
      return_code {
        Mail_System.try_open(options).getOrElse(error("No mail configuration")).server.check()
      }

    val pre_result = return_code { job.hook.pre(options, progress) }

    progress.echo(section("BUILD"))
    val results = progress.interrupt_handler {
      Build.build(
        options ++ job.prefs,
        build_hosts = build_hosts,
        selection = job.selection,
        progress = progress,
        clean_build = job.clean_build,
        afp_root = job.afp_root,
        select_dirs = job.select_dirs,
        numa_shuffling = job.hosts.numa_shuffling,
        max_jobs = job.hosts.max_jobs)
    }

    val post_result = return_code { job.hook.post(options, url, results, progress) }

    val rc = List(mail_result, pre_result, results.rc, post_result).max
    if (rc != Process_Result.RC.ok) {
      progress.echo(section("FAILED"))

      if (mail_result != Process_Result.RC.ok) progress.echo("Mail: FAILED")
      else {
        val mail_system = Mail_System.try_open(options).get
        val content =
          "The job " + job.name + " failed. " + if_proper(url, " View the build at: " + url.get)
        val mail = Mail("Build failed", List(mail_system.to), content, Some(mail_system.from))
        mail_system.server.send(mail)
      }

      if (pre_result != Process_Result.RC.ok) progress.echo("Pre-hook: FAILED")
      for (name <- results.sessions) {
        if (results.cancelled(name)) progress.echo("Session " + name + ": CANCELLED")
        else {
          val result = results(name)
          if (!result.ok) progress.echo("Session " + name + ": FAILED " + result.rc)
        }
      }
      if (post_result != Process_Result.RC.ok) progress.echo("Post-hook: FAILED")
    }

    sys.exit(rc)
  }


  /* Isabelle tool wrapper */

  val isabelle_tool = Isabelle_Tool("build_ci", "builds Isabelle jobs in ci environments",
    Scala_Project.here,
    { args =>
      var options = Options.init()
      val build_hosts = new mutable.ListBuffer[Build_Cluster.Host]
      var url: Option[Url] = None

      val getopts = Getopts("""
Usage: isabelle build_ci [OPTIONS] JOB

  Options are:
    -H HOSTS     host specifications of the form NAMES:PARAMETERS (separated by commas)
    -o OPTION    override Isabelle system OPTION (via NAME=VAL or NAME)
    -u URL       build url

  Runs Isabelle builds in ci environment. For cluster builds, build hosts must
  be passed explicitly (no registry).

  The following build jobs are available:

""" + Library.indent_lines(4, show_jobs) + "\n",
        "H:" -> (arg => build_hosts ++= Build_Cluster.Host.parse(Registry.load(Nil), arg)),
        "o:" -> (arg => options = options + arg),
        "u:" -> (arg => url = Some(Url(arg))))

      val more_args = getopts(args)

      val job =
        more_args match {
          case job :: Nil => the_job(job)
          case _ => getopts.usage()
        }

      val progress = new Console_Progress(verbose = true)

      build_ci(options, job, url = url, build_hosts = build_hosts.toList, progress = progress)
    })
}

class Isabelle_CI_Jobs(val jobs: Build_CI.Job*) extends Isabelle_System.Service

class CI_Jobs extends Isabelle_CI_Jobs(Build_CI.timing)
