/*  Title:      Pure/Admin/news.scala
    Author:     Makarius

Support for the NEWS file.
*/

package isabelle


object NEWS
{
  /* generate HTML version */

  def generate_html()
  {
    val target = Path.explode("~~/doc")
    val target_fonts = target + Path.explode("fonts")
    Isabelle_System.mkdirs(target_fonts)

    for (font <- Isabelle_System.fonts(html = true))
      File.copy(font, target_fonts)

    HTML.write_document(target, "NEWS.html",
      List(HTML.title("NEWS (" + Distribution.version + ")")),
      List(
        HTML.chapter("NEWS"),
        HTML.source(Symbol.decode(File.read(Path.explode("~~/NEWS"))))))
  }


  /* Isabelle tool wrapper */

  val isabelle_tool =
    Isabelle_Tool("news", "generate HTML version of the NEWS file",
      _ => generate_html(), admin = true)
}
