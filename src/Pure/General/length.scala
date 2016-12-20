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

  val encodings: List[(String, Length)] =
    List(
      "UTF-16" -> Length,
      "UTF-8" -> UTF8.Length,
      "codepoints" -> Codepoint.Length,
      "symbols" -> Symbol.Length)

  def encoding(name: String): Length =
    encodings.collectFirst({ case (a, length) if name == a => length }) getOrElse
      error("Bad text length encoding: " + quote(name) +
        " (expected " + commas_quote(encodings.map(_._1)) + ")")
}
