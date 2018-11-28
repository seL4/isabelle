/*  Title:      Pure/System/isabelle_system.scala
    Author:     Makarius

Fonts from the Isabelle system environment, notably the "Isabelle DejaVu"
collection.
*/

package isabelle


object Isabelle_Fonts
{
  /* standard names */

  val mono: String = "Isabelle DejaVu Sans Mono"
  val sans: String = "Isabelle DejaVu Sans"
  val serif: String = "Isabelle DejaVu Serif"


  /* Isabelle system environment */

  def variables(html: Boolean = false): List[String] =
    if (html) List("ISABELLE_FONTS", "ISABELLE_FONTS_HTML") else List("ISABELLE_FONTS")

  def files(
    html: Boolean = false,
    getenv: String => String = Isabelle_System.getenv_strict(_)): List[Path] =
  {
    for {
      variable <- variables(html = html)
      path <- Path.split(getenv(variable))
    } yield path
  }
}
