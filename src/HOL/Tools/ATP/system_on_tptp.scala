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
      List("NoHTML" -> 1, "QuietFlag" -> "-q01")
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
}
