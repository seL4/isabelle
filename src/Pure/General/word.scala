/*  Title:      Pure/General/word.scala
    Author:     Makarius

Support for words within Unicode text.
*/

package isabelle

import java.text.Bidi
import java.util.Locale


object Word {
  /* directionality */

  def bidi_detect(str: String): Boolean =
    str.exists(c => c >= 0x590) && Bidi.requiresBidi(str.toArray, 0, str.length)

  def bidi_override(str: String): String =
    if (bidi_detect(str)) "\u200E\u202D" + str + "\u202C" else str


  /* case */

  def lowercase(str: String): String = str.toLowerCase(Locale.ROOT)
  def uppercase(str: String): String = str.toUpperCase(Locale.ROOT)

  def capitalized(str: String): String =
    if (str.length == 0) str
    else {
      val n = Character.charCount(str.codePointAt(0))
      uppercase(str.substring(0, n)) + lowercase(str.substring(n))
    }

  def perhaps_capitalized(str: String): String =
    if (Codepoint.iterator(str).forall(c => Character.isLowerCase(c) || Character.isDigit(c)))
      capitalized(str)
    else str

  object Case {
    def apply(c: Case, str: String): String =
      c match {
        case Case.lowercase => Word.lowercase(str)
        case Case.uppercase => Word.uppercase(str)
        case Case.capitalized => Word.capitalized(str)
      }
    def unapply(str: String): Option[Case] =
      if (str.nonEmpty) {
        if (Codepoint.iterator(str).forall(Character.isLowerCase)) Some(Case.lowercase)
        else if (Codepoint.iterator(str).forall(Character.isUpperCase)) Some(Case.uppercase)
        else {
          val it = Codepoint.iterator(str)
          if (Character.isUpperCase(it.next()) && it.forall(Character.isLowerCase))
            Some(Case.capitalized)
          else None
        }
      }
      else None
  }

  enum Case { case lowercase, uppercase, capitalized }


  /* sequence of words */

  def implode(words: Iterable[String]): String = words.iterator.mkString(" ")

  def explode(sep: Char => Boolean, text: String): List[String] =
    List.from(
      for (s <- Library.separated_chunks(sep, text) if !s.isEmpty)
        yield s.toString)

  def explode(sep: Char, text: String): List[String] =
    explode(_ == sep, text)

  def explode(text: String): List[String] =
    explode(Character.isWhitespace _, text)

  def informal(text: String): String = implode(explode('_', text))
}
