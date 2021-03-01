/*  Title:      Pure/General/word.scala
    Author:     Makarius

Support for words within Unicode text.
*/

package isabelle

import java.text.Bidi
import java.util.Locale


object Word
{
  /* directionality */

  def bidi_detect(str: String): Boolean =
    str.exists(c => c >= 0x590) && Bidi.requiresBidi(str.toArray, 0, str.length)

  def bidi_override(str: String): String =
    if (bidi_detect(str)) "\u200E\u202D" + str + "\u202C" else str


  /* case */

  def lowercase(str: String): String = str.toLowerCase(Locale.ROOT)
  def uppercase(str: String): String = str.toUpperCase(Locale.ROOT)

  def capitalize(str: String): String =
    if (str.length == 0) str
    else {
      val n = Character.charCount(str.codePointAt(0))
      uppercase(str.substring(0, n)) + lowercase(str.substring(n))
    }

  def perhaps_capitalize(str: String): String =
    if (Codepoint.iterator(str).forall(c => Character.isLowerCase(c) || Character.isDigit(c)))
      capitalize(str)
    else str

  sealed abstract class Case
  case object Lowercase extends Case
  case object Uppercase extends Case
  case object Capitalized extends Case

  object Case
  {
    def apply(c: Case, str: String): String =
      c match {
        case Lowercase => lowercase(str)
        case Uppercase => uppercase(str)
        case Capitalized => capitalize(str)
      }
    def unapply(str: String): Option[Case] =
      if (str.nonEmpty) {
        if (Codepoint.iterator(str).forall(Character.isLowerCase)) Some(Lowercase)
        else if (Codepoint.iterator(str).forall(Character.isUpperCase)) Some(Uppercase)
        else {
          val it = Codepoint.iterator(str)
          if (Character.isUpperCase(it.next()) && it.forall(Character.isLowerCase))
            Some(Capitalized)
          else None
        }
      }
      else None
  }


  /* sequence of words */

  def implode(words: Iterable[String]): String = words.iterator.mkString(" ")

  def explode(sep: Char => Boolean, text: String): List[String] =
    Library.separated_chunks(sep, text).map(_.toString).filter(_ != "").toList

  def explode(sep: Char, text: String): List[String] =
    explode(_ == sep, text)

  def explode(text: String): List[String] =
    explode(Character.isWhitespace _, text)


  /* brackets */

  val open_brackets = "([{«‹⟨⌈⌊⦇⟦⦃⟪"
  val close_brackets = ")]}»›⟩⌉⌋⦈⟧⦄⟫"
}
