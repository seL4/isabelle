/*  Title:      Pure/System/isabelle_system.scala
    Author:     Makarius

Fonts from the Isabelle system environment, notably the "Isabelle DejaVu"
collection.
*/

package isabelle


import java.awt.{Font, GraphicsEnvironment}


object Isabelle_Fonts
{
  /* standard names */

  val mono: String = "Isabelle DejaVu Sans Mono"
  val sans: String = "Isabelle DejaVu Sans"
  val serif: String = "Isabelle DejaVu Serif"


  /* environment entries */

  object Entry
  {
    object Ordering extends scala.math.Ordering[Entry]
    {
      def compare(entry1: Entry, entry2: Entry): Int =
        entry1.family compare entry2.family match {
          case 0 => entry1.style compare entry2.style
          case ord => ord
        }
    }
  }

  sealed case class Entry(path: Path, hidden: Boolean = false)
  {
    lazy val bytes: Bytes = Bytes.read(path)
    lazy val font: Font = Font.createFont(Font.TRUETYPE_FONT, path.file)

    def family: String = font.getFamily
    def name: String = font.getFontName
    def style: Int =
      (if (is_bold) Font.BOLD else 0) +
      (if (is_italic) Font.ITALIC else 0)

    // educated guess for style: Font.createFont always produces Font.PLAIN
    private lazy val name_lowercase = Word.lowercase(name)
    def is_bold: Boolean =
      name_lowercase.containsSlice("bold")
    def is_italic: Boolean =
      name_lowercase.containsSlice("italic") ||
      name_lowercase.containsSlice("oblique")
  }

  def make_entries(
    getenv: String => String = Isabelle_System.getenv_strict(_),
    hidden: Boolean = false): List[Entry] =
  {
    Path.split(getenv("ISABELLE_FONTS")).map(Entry(_)) :::
    (if (hidden) Path.split(getenv("ISABELLE_FONTS_HIDDEN")).map(Entry(_, hidden = true)) else Nil)
  }

  private lazy val all_fonts: List[Entry] =
    make_entries(hidden = true).sorted(Entry.Ordering)

  def fonts(hidden: Boolean = false): List[Entry] =
    if (hidden) all_fonts else all_fonts.filter(entry => !entry.hidden)


  /* system init */

  def init(): Unit =
  {
    val ge = GraphicsEnvironment.getLocalGraphicsEnvironment()
    for (entry <- fonts()) ge.registerFont(entry.font)
  }
}
