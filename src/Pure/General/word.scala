/*  Title:      Pure/General/word.scala
    Module:     PIDE
    Author:     Makarius

Support for plain text words.
*/

package isabelle


import java.util.Locale


object Word
{
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

  def plain_words(str: String): String =
    space_explode('_', str).mkString(" ")
}

