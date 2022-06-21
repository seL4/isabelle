/*  Title:      Pure/Admin/ci_profile.scala
    Author:     Lars Hupel and Fabian Huch, TU Munich

Build profile for continuous integration services.
*/

package isabelle


import java.time.{Instant, ZoneId}
import java.time.format.DateTimeFormatter
import java.util.{Properties => JProperties, Map => JMap}


object CI_Profile {

  /* Result */

  case class Result(rc: Int)
  case object Result {
    def ok: Result = Result(Process_Result.RC.ok)
    def error: Result = Result(Process_Result.RC.error)
  }


  /* Profile */

  case class Profile(threads: Int, jobs: Int, numa: Boolean)

  object Profile {
    def from_host: Profile = {
      Isabelle_System.hostname() match {
        case "hpcisabelle" => Profile(8, 8, numa = true)
        case "lxcisa1" => Profile(4, 10, numa = false)
        case _ => Profile(2, 2, numa = false)
      }
    }
  }


  /* Config */

  case class Build_Config(
    documents: Boolean = true,
    clean: Boolean = true,
    include: List[Path] = Nil,
    select: List[Path] = Nil,
    pre_hook: () => Result = () => { Result.ok },
    post_hook: Build.Results => Result = { _ => Result.ok },
    selection: Sessions.Selection = Sessions.Selection.empty
  )


  /* Status */

  sealed abstract class Status(val str: String) {
    def merge(that: Status): Status = (this, that) match {
      case (Ok, s) => s
      case (Failed, _) => Failed
      case (Skipped, Failed) => Failed
      case (Skipped, _) => Skipped
    }
  }

  object Status {
    def merge(statuses: List[Status]): Status =
      statuses.foldLeft(Ok: Status)(_ merge _)

    def from_results(results: Build.Results, session: String): Status =
      if (results.cancelled(session))
        Skipped
      else if (results(session).ok)
        Ok
      else
        Failed
  }

  case object Ok extends Status("ok")
  case object Skipped extends Status("skipped")
  case object Failed extends Status("failed")


  private def load_properties(): JProperties = {
    val props = new JProperties()
    val file_name = Isabelle_System.getenv("ISABELLE_CI_PROPERTIES")

    if (file_name != "") {
      val file = Path.explode(file_name).file
      if (file.exists())
        props.load(new java.io.FileReader(file))
      props
    }
    else
      props
  }

  private def compute_timing(results: Build.Results, group: Option[String]): Timing = {
    val timings = results.sessions.collect {
      case session if group.forall(results.info(session).groups.contains(_)) =>
        results(session).timing
    }
    timings.foldLeft(Timing.zero)(_ + _)
  }

  private def with_documents(options: Options, config: Build_Config): Options = {
    if (config.documents)
      options
        .bool.update("browser_info", true)
        .string.update("document", "pdf")
        .string.update("document_variants", "document:outline=/proof,/ML")
    else
      options
  }

  def hg_id(path: Path): String =
    Mercurial.repository(path).id()

  def print_section(title: String): Unit =
    println(s"\n=== $title ===\n")

  def build(profile: Profile, config: Build_Config): Unit = {
    val isabelle_home = Path.explode(Isabelle_System.getenv_strict("ISABELLE_HOME"))
    val isabelle_id = hg_id(isabelle_home)

    val start_time = Instant.now().atZone(ZoneId.systemDefault).format(DateTimeFormatter.RFC_1123_DATE_TIME)

    print_section("CONFIGURATION")
    println(Build_Log.Settings.show())
    val props = load_properties()
    System.getProperties.asInstanceOf[JMap[AnyRef, AnyRef]].putAll(props)

    val options =
      with_documents(Options.init(), config)
        .int.update("parallel_proofs", 1)
        .int.update("threads", profile.threads)

    println(s"jobs = ${profile.jobs}, threads = ${profile.threads}, numa = ${profile.numa}")

    print_section("BUILD")
    println(s"Build started at $start_time")
    println(s"Isabelle id $isabelle_id")
    val pre_result = config.pre_hook()

    print_section("LOG")
    val (results, elapsed_time) = {
      val progress = new Console_Progress(verbose = true)
      val start_time = Time.now()
      val results = progress.interrupt_handler {
        Build.build(
          options + "system_heaps",
          selection = config.selection,
          progress = progress,
          clean_build = config.clean,
          verbose = true,
          numa_shuffling = profile.numa,
          max_jobs = profile.jobs,
          dirs = config.include,
          select_dirs = config.select)
      }
      val end_time = Time.now()
      (results, end_time - start_time)
    }

    print_section("TIMING")

    val groups = results.sessions.map(results.info).flatMap(_.groups)
    for (group <- groups)
      println(s"Group $group: " + compute_timing(results, Some(group)).message_resources)

    val total_timing = compute_timing(results, None).copy(elapsed = elapsed_time)
    println("Overall: " + total_timing.message_resources)

    if (!results.ok) {
      print_section("FAILED SESSIONS")

      for (name <- results.sessions) {
        if (results.cancelled(name)) {
          println(s"Session $name: CANCELLED")
        }
        else {
          val result = results(name)
          if (!result.ok)
            println(s"Session $name: FAILED ${ result.rc }")
        }
      }
    }

    val post_result = config.post_hook(results)

    System.exit(List(pre_result.rc, results.rc, post_result.rc).max)
  }
}