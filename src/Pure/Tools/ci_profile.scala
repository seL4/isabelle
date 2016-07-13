/*  Title:      Pure/Tools/ci_profile.scala
    Author:     Lars Hupel

Build profile for continuous integration services.
*/

package isabelle


import java.time._
import java.time.format.DateTimeFormatter
import java.util.{Properties => JProperties}


abstract class CI_Profile extends Isabelle_Tool.Body
{

  private def print_variable(name: String): Unit =
  {
    val value = Isabelle_System.getenv_strict(name)
    println(name + "=" + Outer_Syntax.quote_string(value))
  }

  private def build(options: Options): (Build.Results, Time) =
  {
    val progress = new Console_Progress(true)
    val start_time = Time.now()
    val results = progress.interrupt_handler {
      Build.build_selection(
        options = options,
        progress = progress,
        clean_build = true,
        verbose = true,
        max_jobs = jobs,
        dirs = include,
        select_dirs = select,
        system_mode = true,
        selection = select_sessions _)
    }
    val end_time = Time.now()
    (results, end_time - start_time)
  }

  private def load_properties(): JProperties =
  {
    val props = new JProperties()
    val file_name = Isabelle_System.getenv("ISABELLE_CI_PROPERTIES")

    if (file_name != "")
    {
      val file = Path.explode(file_name).file
      if (file.exists())
        props.load(new java.io.FileReader(file))
      props
    }
    else
      props
  }

  private def compute_timing(results: Build.Results, group: Option[String]): Timing =
  {
    val timings = results.sessions.collect {
      case session if group.forall(results.info(session).groups.contains(_)) =>
        results(session).timing
    }
    (Timing.zero /: timings)(_ + _)
  }


  final def hg_id(path: Path): String =
    Isabelle_System.hg("id -i", path.file).out

  final def print_section(title: String): Unit =
    println(s"\n=== $title ===\n")


  final val isabelle_home = Path.explode(Isabelle_System.getenv_strict("ISABELLE_HOME"))
  final val isabelle_id = hg_id(isabelle_home)
  final val start_time = Instant.now().atZone(ZoneId.systemDefault).format(DateTimeFormatter.RFC_1123_DATE_TIME)


  override final def apply(args: List[String]): Unit =
  {
    print_section("CONFIGURATION")
    List("ML_PLATFORM", "ML_HOME", "ML_SYSTEM", "ML_OPTIONS").foreach(print_variable)
    val props = load_properties()
    System.getProperties().putAll(props)

    val options =
      Options.init()
        .bool.update("browser_info", true)
        .string.update("document", "pdf")
        .string.update("document_variants", "document:outline=/proof,/ML")
        .int.update("parallel_proofs", 2)
        .int.update("threads", threads)

    print_section("BUILD")
    println(s"Build started at $start_time")
    println(s"Isabelle id $isabelle_id")
    pre_hook(args)

    print_section("LOG")
    val (results, elapsed_time) = build(options)

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
            println(s"Session $name: FAILED ${result.rc}")
        }
      }
    }

    post_hook(results)

    System.exit(results.rc)
  }


  /* profile */

  def threads: Int
  def jobs: Int
  def include: List[Path]
  def select: List[Path]

  def pre_hook(args: List[String]): Unit
  def post_hook(results: Build.Results): Unit

  def select_sessions(tree: Sessions.Tree): (List[String], Sessions.Tree)

}
