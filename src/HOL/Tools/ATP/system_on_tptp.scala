/*  Title:      HOL/Tools/ATP/system_on_tptp.scala
    Author:     Makarius

Support for remote ATPs via SystemOnTPTP.
*/

package isabelle.atp

import isabelle._

import java.net.URL


object SystemOnTPTP
{
  def get_url(options: Options): URL = Url(options.string("SystemOnTPTP"))

  def proper_lines(text: String): List[String] =
    Library.trim_split_lines(text).filterNot(_.startsWith("%"))

  def list_systems(url: URL): List[String] =
  {
    val result =
      HTTP.Client.post(url, user_agent = "Sledgehammer", parameters =
        List("NoHTML" -> 1,
          "QuietFlag" -> "-q0",
          "SubmitButton" -> "ListSystems",
          "ListStatus" -> "READY"))
    proper_lines(result.text)
  }

  object List_Systems extends Scala.Fun("SystemOnTPTP.list_systems", thread = true)
  {
    val here = Scala_Project.here
    def apply(url: String): String = cat_lines(list_systems(Url(url)))
  }
}
