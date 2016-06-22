/*  Title:      Pure/Tools/ci_profile.scala
    Author:     Lars Hupel

Build profile for continuous integration services.
*/

package isabelle


import java.util.{Properties => JProperties}


abstract class CI_Profile extends Isabelle_Tool.Body
{

  private def print_variable(name: String): Unit =
  {
    val value = Isabelle_System.getenv_strict(name)
    println(name + "=" + Outer_Syntax.quote_string(value))
  }

  protected def hg_id(path: Path): String =
    Isabelle_System.hg("id -i", path.file).out

  private def build(options: Options): (Build.Results, Time) =
  {
    val start_time = Time.now()
    val progress = new Console_Progress(true)
    val results = progress.interrupt_handler {
      Build.build(
        options = options,
        progress = progress,
        clean_build = true,
        verbose = true,
        max_jobs = jobs,
        dirs = include,
        select_dirs = select,
        session_groups = groups,
        all_sessions = all,
        exclude_session_groups = exclude,
        system_mode = true
      )
    }
    val end_time = Time.now()
    (results, end_time - start_time)
  }

  private def load_properties(): JProperties =
  {
    val props = new JProperties()
    val file = Path.explode(Isabelle_System.getenv_strict("ISABELLE_CI_PROPERTIES")).file
    if (file.exists())
      props.load(new java.io.FileReader(file))
    props
  }

  protected def print_section(title: String): Unit =
    println(s"\n=== $title ===\n")


  override final def apply(args: List[String]): Unit =
  {
    print_section("CONFIGURATION")
    List("ML_PLATFORM", "ML_HOME", "ML_SYSTEM", "ML_OPTIONS").foreach(print_variable)
    val props = load_properties()
    System.getProperties().putAll(props)

    val isabelle_home = Path.explode(Isabelle_System.getenv_strict("ISABELLE_HOME"))

    val options =
      Options.init()
        .bool.update("browser_info", true)
        .string.update("document", "pdf")
        .string.update("document_variants", "document:outline=/proof,/ML")
        .int.update("parallel_proofs", 2)
        .int.update("threads", threads)

    print_section("BUILD")
    println(s"Build for Isabelle id ${hg_id(isabelle_home)}")
    pre_hook(args)

    val (results, elapsed_time) = build(options)

    print_section("TIMING")
    val total_timing =
      (Timing.zero /: results.sessions.iterator.map(a => results(a).timing))(_ + _).
        copy(elapsed = elapsed_time)
    println(total_timing.message_resources)

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
  def all: Boolean
  def groups: List[String]
  def exclude: List[String]
  def include: List[Path]
  def select: List[Path]

  def pre_hook(args: List[String]): Unit
  def post_hook(results: Build.Results): Unit

}
