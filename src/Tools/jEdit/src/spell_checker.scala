/*  Title:      Tools/jEdit/src/spell_checker.scala
    Author:     Makarius

Spell-checker based on JOrtho (see http://sourceforge.net/projects/jortho).
*/

package isabelle.jedit


import isabelle._

import java.lang.Class
import java.net.URL


object Spell_Checker
{
  def known_dictionaries: List[String] =
    space_explode(',', Isabelle_System.getenv_strict("JORTHO_DICTIONARIES"))

  def apply(dict: String): Spell_Checker =
    if (known_dictionaries.contains(dict))
      new Spell_Checker(
        dict, classOf[com.inet.jortho.SpellChecker].getResource("dictionary_" + dict + ".ortho"))
    else error("Unknown spell-checker dictionary " + quote(dict))

  def apply(dict: URL): Spell_Checker =
    new Spell_Checker(dict.toString, dict)
}

class Spell_Checker private(dict_name: String, dict: URL)
{
  override def toString: String = "Spell_Checker(" + dict_name + ")"

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

  def check(word: String): Boolean =
  {
    val m = dictionary.getClass.getSuperclass.getDeclaredMethod("exist", classOf[String])
    m.setAccessible(true)
    m.invoke(dictionary, word).asInstanceOf[java.lang.Boolean].booleanValue
  }

  def complete(word: String): List[String] =
  {
    val m = dictionary.getClass.getSuperclass.
      getDeclaredMethod("searchSuggestions", classOf[String])
    m.setAccessible(true)
    m.invoke(dictionary, word).asInstanceOf[java.util.List[AnyRef]].toArray.toList.map(_.toString)
  }
}

