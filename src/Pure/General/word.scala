/*  Title:      Pure/General/word.scala
    Module:     PIDE
    Author:     Makarius

Support for plain text words.
*/

package isabelle


import java.util.Locale


object Word
{
  /* case */

  def lowercase(str: String): String = str.toLowerCase(Locale.ROOT)
  def uppercase(str: String): String = str.toUpperCase(Locale.ROOT)

  def capitalize(str: String): String =
    if (str.length == 0) str
    else uppercase(str.substring(0, 1)) + str.substring(1)

  def is_capitalized(str: String): Boolean =
    str.length > 0 &&
    Character.isUpperCase(str(0)) && str.substring(1).forall(Character.isLowerCase(_))

  def is_all_caps(str: String): Boolean =
    str.length > 0 && str.forall(Character.isUpperCase(_))


  /* sequence of words */

  def implode(words: Iterable[String]): String = words.iterator.mkString(" ")

  def explode(sep: Char => Boolean, text: String): List[String] =
    Library.separated_chunks(sep, text).map(_.toString).filter(_ != "").toList

  def explode(sep: Char, text: String): List[String] =
    explode(_ == sep, text)

  def explode(text: String): List[String] =
    explode(Symbol.is_ascii_blank(_), text)
}

