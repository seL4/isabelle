/*  Title:      Pure/System/isabelle_system.scala
    Author:     Makarius

Fonts from the Isabelle system environment, notably the "Isabelle DejaVu"
collection.
*/

package isabelle


import java.awt.Font


object Isabelle_Fonts
{
  /* standard names */

  val mono: String = "Isabelle DejaVu Sans Mono"
  val sans: String = "Isabelle DejaVu Sans"
  val serif: String = "Isabelle DejaVu Serif"


  /* environment entries */

  sealed case class Entry(path: Path, html: Boolean = false)
  {
    def bytes: Bytes = Bytes.read(path)

    lazy val font: Font = Font.createFont(Font.TRUETYPE_FONT, path.file)
    def family: String = font.getFamily
    def name: String = font.getFontName

    // educated guessing
    private lazy val name_lowercase = Word.lowercase(name)
    def is_bold: Boolean =
      name_lowercase.containsSlice("bold")
    def is_italic: Boolean =
      name_lowercase.containsSlice("italic") || name_lowercase.containsSlice("oblique")
  }

  def make_entries(
    getenv: String => String = Isabelle_System.getenv_strict(_),
    html: Boolean = false): List[Entry] =
  {
    Path.split(getenv("ISABELLE_FONTS")).map(Entry(_)) :::
    (if (html) Path.split(getenv("ISABELLE_FONTS_HTML")).map(Entry(_, html = true)) else Nil)
  }

  private lazy val all_fonts: List[Entry] = make_entries(html = true)

  def fonts(html: Boolean = false): List[Entry] =
    if (html) all_fonts else all_fonts.filter(entry => !entry.html)
}
