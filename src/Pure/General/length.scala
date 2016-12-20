/*  Title:      Pure/General/length.scala
    Author:     Makarius

Text length wrt. encoding.
*/

package isabelle


trait Length
{
  def apply(text: String): Int
  def offset(text: String, i: Int): Option[Text.Offset]
}

object Length extends Length
{
  def apply(text: String): Int = text.length
  def offset(text: String, i: Int): Option[Text.Offset] =
    if (0 <= i && i <= text.length) Some(i) else None

  def encoding(name: String): Length =
    name match {
      case "UTF-8" => UTF8.Length
      case "UTF-16" => Length
      case "codepoints" => Codepoint.Length
      case "symbols" => Symbol.Length
      case _ =>
        error("Bad text encoding: " + name + " (expected UTF-8, UTF-16, codepoints, symbols)")
    }
}
