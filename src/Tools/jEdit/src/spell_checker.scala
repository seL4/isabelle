/*  Title:      Tools/jEdit/src/spell_checker.scala
    Author:     Makarius

Spell checker based on JOrtho (see http://sourceforge.net/projects/jortho).
*/

package isabelle.jedit


import isabelle._

import java.lang.Class
import java.util.Locale
import java.text.BreakIterator

import scala.collection.mutable
import scala.swing.ComboBox
import scala.annotation.tailrec


object Spell_Checker
{
  /* dictionary consisting of word list */

  class Dictionary private [Spell_Checker](path: Path)
  {
    val lang = path.split_ext._1.base.implode
    override def toString: String = lang

    val locale: Locale =
      space_explode('_', lang) match {
        case l :: _ => Locale.forLanguageTag(l)
        case Nil => Locale.ENGLISH
      }

    def load_words: List[String] =
      path.split_ext._2 match {
        case "gz" => split_lines(File.read_gzip(path))
        case "" => split_lines(File.read(path))
        case ext => error("Bad file extension for dictionary " + path)
      }
  }


  /* known dictionaries */

  def dictionaries(): List[Dictionary] =
    for {
      path <- Path.split(Isabelle_System.getenv("JORTHO_DICTIONARIES"))
      if path.is_file
    } yield new Dictionary(path)

  def dictionaries_selector(): Option_Component =
  {
    Swing_Thread.require()

    val option_name = "spell_checker_language"
    val opt = PIDE.options.value.check_name(option_name)

    val entries = dictionaries()
    val component = new ComboBox(entries) with Option_Component {
      name = option_name
      val title = opt.title()
      def load: Unit =
      {
        val lang = PIDE.options.string(option_name)
        entries.find(_.lang == lang) match {
          case Some(entry) => selection.item = entry
          case None =>
        }
      }
      def save: Unit = PIDE.options.string(option_name) = selection.item.lang
    }

    component.load()
    component.tooltip = opt.print_default
    component
  }


  /* create spell checker */

  def apply(dict: Dictionary): Spell_Checker = new Spell_Checker(dict)
}


class Spell_Checker private(dict: Spell_Checker.Dictionary)
{
  override def toString: String = dict.toString

  private val dictionary =
  {
    val factory_class = Class.forName("com.inet.jortho.DictionaryFactory")
    val factory_cons = factory_class.getConstructor()
    factory_cons.setAccessible(true)
    val factory = factory_cons.newInstance()

    val add = factory_class.getDeclaredMethod("add", classOf[String])
    add.setAccessible(true)
    dict.load_words.foreach(add.invoke(factory, _))

    val create = factory_class.getDeclaredMethod("create")
    create.setAccessible(true)
    create.invoke(factory)
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
    Library.is_all_caps(word) && contains(Library.lowercase(word, dict.locale)) ||
    Library.is_capitalized(word) &&
      (contains(Library.lowercase(word, dict.locale)) ||
       contains(Library.uppercase(word, dict.locale)))

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
    var offset = 0

    def apostrophe(c: Int): Boolean =
      c == '\'' && (offset + 1 == text.length || text(offset + 1) != '\'')

    @tailrec def scan(pred: Int => Boolean)
    {
      if (offset < text.length) {
        val c = text.codePointAt(offset)
        if (pred(c)) {
          offset += Character.charCount(c)
          scan(pred)
        }
      }
    }

    while (offset < text.length) {
      scan(c => !Character.isLetter(c))
      val start = offset
      scan(c => Character.isLetterOrDigit(c) || apostrophe(c))
      val stop = offset
      if (stop - start >= 2 && !check(text.substring(start, stop)))
        result += Text.Range(start, stop)
    }
    result.toList
  }
}


class Spell_Checker_Variable
{
  private val no_spell_checker: (String, Option[Spell_Checker]) = ("", None)
  private var current_spell_checker = no_spell_checker

  def get: Option[Spell_Checker] = synchronized { current_spell_checker._2 }

  def update(options: Options): Unit = synchronized {
    if (options.bool("spell_checker")) {
      val lang = options.string("spell_checker_language")
      if (current_spell_checker._1 != lang) {
        Spell_Checker.dictionaries.find(_.lang == lang) match {
          case Some(dict) =>
            val spell_checker =
              Exn.capture { Spell_Checker(dict) } match {
                case Exn.Res(spell_checker) => Some(spell_checker)
                case Exn.Exn(_) => None
              }
            current_spell_checker = (lang, spell_checker)
          case None =>
            current_spell_checker = no_spell_checker
        }
      }
    }
    else current_spell_checker = no_spell_checker
  }
}
