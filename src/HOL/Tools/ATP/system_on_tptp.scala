/*  Title:      HOL/Tools/ATP/system_on_tptp.scala
    Author:     Makarius

Support for remote ATPs via SystemOnTPTP.
*/

package isabelle.atp

import isabelle._

import java.net.URL


object SystemOnTPTP
{
  /* requests */

  def get_url(options: Options): URL = Url(options.string("SystemOnTPTP"))

  def post_request(
    url: URL,
    parameters: List[(String, Any)],
    timeout: Time = HTTP.Client.default_timeout): HTTP.Content =
  {
    val parameters0 =
      List("NoHTML" -> 1, "QuietFlag" -> "-q0")
        .filterNot(p0 => parameters.exists(p => p0._1 == p._1))
    try {
      HTTP.Client.post(url, parameters0 ::: parameters,
        timeout = timeout, user_agent = "Sledgehammer")
    }
    catch { case ERROR(msg) => cat_error("Failed to access SystemOnTPTP server", msg) }
  }


  /* list systems */

  def list_systems(url: URL): HTTP.Content =
    post_request(url, List("SubmitButton" -> "ListSystems", "ListStatus" -> "READY"))

  object List_Systems extends Scala.Fun("SystemOnTPTP.list_systems", thread = true)
  {
    val here = Scala_Project.here
    def apply(url: String): String = list_systems(Url(url)).string
  }


  /* run system */

  def run_system(url: URL,
    system: String,
    problem: String,
    extra: String = "",
    quiet: String = "01",
    timeout: Time = Time.seconds(60)): HTTP.Content =
  {
    val paramaters =
      List(
        "SubmitButton" -> "RunSelectedSystems",
        "ProblemSource" -> "FORMULAE",
        "FORMULAEProblem" -> problem,
        "ForceSystem" -> "-force",
        "System___" + system -> system,
        "TimeLimit___" + system -> timeout.seconds.ceil.toLong,
        "Command___" + system -> extra,
        "QuietFlag" -> ("-q" + quiet))
    post_request(url, paramaters, timeout = timeout + Time.seconds(15))
  }

  object Run_System extends Scala.Fun("SystemOnTPTP.run_system", thread = true)
  {
    val here = Scala_Project.here
    def apply(arg: String): String =
    {
      val List(url, system, problem, extra, Value.Int(timeout)) = Library.split_strings0(arg)
      val res = run_system(Url(url), system, problem, extra = extra, timeout = Time.ms(timeout))

      val bad_prover = "WARNING: " + system + " does not exist"
      if (res.trim_split_lines.exists(_.startsWith(bad_prover))) {
        error("The ATP " + quote(system) + " is not available at SystemOnTPTP")
      }
      else Library.cat_strings0(List(res.string, res.elapsed_time.ms.toString))
    }
  }
}
