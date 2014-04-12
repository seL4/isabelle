/*  Title:      Tools/jEdit/src/spell_checker.scala
    Author:     Makarius

Spell-checker based on JOrtho (see http://sourceforge.net/projects/jortho).
*/

package isabelle.jedit


import isabelle._

import java.lang.Class
import java.net.URL
import java.util.Locale
import java.text.BreakIterator

import scala.collection.mutable


object Spell_Checker
{
  def known_dictionaries: List[String] =
    space_explode(',', Isabelle_System.getenv_strict("JORTHO_DICTIONARIES"))

  def apply(lang: String): Spell_Checker =
    if (known_dictionaries.contains(lang))
      new Spell_Checker(
        lang, Locale.forLanguageTag(lang),
        classOf[com.inet.jortho.SpellChecker].getResource("dictionary_" + lang + ".ortho"))
    else error("Unknown spell-checker dictionary for " + quote(lang))

  def apply(lang: String, locale: Locale, dict: URL): Spell_Checker =
    new Spell_Checker(lang, locale, dict)
}

class Spell_Checker private(lang: String, locale: Locale, dict: URL)
{
  override def toString: String = "Spell_Checker(" + lang + ")"

  private val dictionary =
  {
    val factory_class = Class.forName("com.inet.jortho.DictionaryFactory")
    val factory_cons = factory_class.getConstructor()
    factory_cons.setAccessible(true)
    val factory = factory_cons.newInstance()

    val load_word_list = factory_class.getDeclaredMethod("loadWordList", classOf[URL])
    load_word_list.setAccessible(true)
    load_word_list.invoke(factory, dict)

    val create = factory_class.getDeclaredMethod("create")
    create.setAccessible(true)
    create.invoke(factory)
  }

  def load(file_name: String)
  {
    val m = dictionary.getClass.getDeclaredMethod("load", classOf[String])
    m.setAccessible(true)
    m.invoke(dictionary, file_name)
  }

  def save(file_name: String)
  {
    val m = dictionary.getClass.getDeclaredMethod("save", classOf[String])
    m.setAccessible(true)
    m.invoke(dictionary, file_name)
  }

  def add(word: String)
  {
    val m = dictionary.getClass.getDeclaredMethod("add", classOf[String])
    m.setAccessible(true)
    m.invoke(dictionary, word)
  }

  def contains(word: String): Boolean =
  {
    val m = dictionary.getClass.getSuperclass.getDeclaredMethod("exist", classOf[String])
    m.setAccessible(true)
    m.invoke(dictionary, word).asInstanceOf[java.lang.Boolean].booleanValue
  }

  def check(word: String): Boolean =
    contains(word) ||
    Library.is_all_caps(word) && contains(Library.lowercase(word, locale)) ||
    Library.is_capitalized(word) &&
      (contains(Library.lowercase(word, locale)) || contains(Library.uppercase(word, locale)))

  def complete(word: String): List[String] =
  {
    val m = dictionary.getClass.getSuperclass.
      getDeclaredMethod("searchSuggestions", classOf[String])
    m.setAccessible(true)
    m.invoke(dictionary, word).asInstanceOf[java.util.List[AnyRef]].toArray.toList.map(_.toString)
  }

  def bad_words(text: String): List[Text.Range] =
  {
    val result = new mutable.ListBuffer[Text.Range]

    val it = BreakIterator.getWordInstance(locale)
    it.setText(text)

    var i = 0
    var j = it.next
    while (j != BreakIterator.DONE) {
      val word = text.substring(i, j)
      if (word.length >= 2 && Character.isLetter(word(0)) && !check(word))
        result += Text.Range(i, j)
      i = j
      j = it.next
    }
    result.toList
  }
}

