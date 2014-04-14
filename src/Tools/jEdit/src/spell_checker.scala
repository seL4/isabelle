/*  Title:      Tools/jEdit/src/spell_checker.scala
    Author:     Makarius

Spell checker with completion, based on JOrtho (see
http://sourceforge.net/projects/jortho).
*/

package isabelle.jedit


import isabelle._

import java.lang.Class

import scala.collection.mutable
import scala.swing.ComboBox
import scala.annotation.tailrec


object Spell_Checker
{
  /* marked words within text */

  def marked_words(base: Text.Offset, text: String, mark: Text.Info[String] => Boolean)
    : List[Text.Info[String]] =
  {
    val result = new mutable.ListBuffer[Text.Info[String]]
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
      if (stop - start >= 2) {
        val info = Text.Info(Text.Range(base + start, base + stop), text.substring(start, stop))
        if (mark(info)) result += info
      }
    }
    result.toList
  }


  /* dictionary consisting of word list */

  class Dictionary private [Spell_Checker](path: Path)
  {
    val lang = path.split_ext._1.base.implode
    override def toString: String = lang

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

    val option_name = "spell_checker_dictionary"
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

  def apply(dictionary: Dictionary): Spell_Checker = new Spell_Checker(dictionary)
}


class Spell_Checker private(dictionary: Spell_Checker.Dictionary)
{
  override def toString: String = dictionary.toString

  private val dict =
  {
    val factory_class = Class.forName("com.inet.jortho.DictionaryFactory")
    val factory_cons = factory_class.getConstructor()
    factory_cons.setAccessible(true)
    val factory = factory_cons.newInstance()

    val add = factory_class.getDeclaredMethod("add", classOf[String])
    add.setAccessible(true)
    dictionary.load_words.foreach(add.invoke(factory, _))

    val create = factory_class.getDeclaredMethod("create")
    create.setAccessible(true)
    create.invoke(factory)
  }

  def add(word: String)
  {
    val m = dict.getClass.getDeclaredMethod("add", classOf[String])
    m.setAccessible(true)
    m.invoke(dict, word)
  }

  def contains(word: String): Boolean =
  {
    val m = dict.getClass.getSuperclass.getDeclaredMethod("exist", classOf[String])
    m.setAccessible(true)
    m.invoke(dict, word).asInstanceOf[java.lang.Boolean].booleanValue
  }

  def check(word: String): Boolean =
    contains(word) ||
    Library.is_all_caps(word) && contains(Library.lowercase(word)) ||
    Library.is_capitalized(word) &&
      (contains(Library.lowercase(word)) || contains(Library.uppercase(word)))

  def complete(word: String): List[String] =
    if (check(word)) Nil
    else {
      val m = dict.getClass.getSuperclass. getDeclaredMethod("searchSuggestions", classOf[String])
      m.setAccessible(true)
      m.invoke(dict, word).asInstanceOf[java.util.List[AnyRef]].toArray.toList.map(_.toString)
    }

  def marked_words(base: Text.Offset, text: String): List[Text.Info[String]] =
    Spell_Checker.marked_words(base, text, info => !check(info.info))
}


class Spell_Checker_Variable
{
  private val no_spell_checker: (String, Option[Spell_Checker]) = ("", None)
  private var current_spell_checker = no_spell_checker

  def get: Option[Spell_Checker] = synchronized { current_spell_checker._2 }

  def update(options: Options): Unit = synchronized {
    if (options.bool("spell_checker")) {
      val lang = options.string("spell_checker_dictionary")
      if (current_spell_checker._1 != lang) {
        Spell_Checker.dictionaries.find(_.lang == lang) match {
          case Some(dictionary) =>
            val spell_checker =
              Exn.capture { Spell_Checker(dictionary) } match {
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
