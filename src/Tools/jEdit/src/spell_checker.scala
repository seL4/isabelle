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
import scala.collection.immutable.{SortedSet, SortedMap}


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


  /* dictionary -- include/exclude word list */

  private val USER_DICTIONARIES = Path.explode("$ISABELLE_HOME_USER/dictionaries")

  class Dictionary private [Spell_Checker](path: Path)
  {
    val lang = path.split_ext._1.base.implode
    override def toString: String = lang

    private val user_path = USER_DICTIONARIES + Path.basic(lang)

    def load(): (List[String], List[String], List[String]) =
    {
      val main = split_lines(File.read_gzip(path))

      val user_entries =
        if (user_path.is_file)
          for {
            raw_line <- split_lines(File.read(user_path))
            line = raw_line.trim
            if line != "" && !line.startsWith("#")
            entry =
              Library.try_unprefix("-", line) match {
                case Some(s) => (s, false)
                case None => (line, true)
              }
          } yield entry
        else Nil
      val user = SortedMap.empty[String, Boolean] ++ user_entries
      val include = user.toList.filter(_._2).map(_._1)
      val exclude = user.toList.filterNot(_._2).map(_._1)

      (main, include, exclude)
    }

    def save(include: List[String], exclude: List[String])
    {
      if (!include.isEmpty || !exclude.isEmpty || user_path.is_file) {
        val header = """# Spell-checker dictionary
#
#   * each line contains at most one word
#   * extra blanks are ignored
#   * lines starting with "#" are ignored
#   * lines starting with "-" indicate excluded words
#   * later entries take precedence
#
"""
        Isabelle_System.mkdirs(USER_DICTIONARIES)
        File.write(user_path, header + cat_lines(include ::: exclude.map("-" + _)))
      }
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

  private var dict = new Object
  private var include_set = SortedSet.empty[String]
  private var exclude_set = SortedSet.empty[String]

  private def make_dict()
  {
    val factory_class = Class.forName("com.inet.jortho.DictionaryFactory")
    val factory_cons = factory_class.getConstructor()
    factory_cons.setAccessible(true)
    val factory = factory_cons.newInstance()

    val add = factory_class.getDeclaredMethod("add", classOf[String])
    add.setAccessible(true)

    val (main, include, exclude) = dictionary.load()
    include_set = SortedSet.empty[String] ++ include
    exclude_set = SortedSet.empty[String] ++ exclude

    for {
      word <- main.iterator ++ include.iterator
      if !exclude_set.contains(word)
    } add.invoke(factory, word)

    val create = factory_class.getDeclaredMethod("create")
    create.setAccessible(true)
    dict = create.invoke(factory)
  }
  make_dict()

  def save()
  {
    dictionary.save(include_set.toList, exclude_set.toList)
  }

  def include(word: String)
  {
    include_set += word
    exclude_set -= word

    val m = dict.getClass.getDeclaredMethod("add", classOf[String])
    m.setAccessible(true)
    m.invoke(dict, word)

    save()
  }

  def exclude(word: String)
  {
    include_set -= word
    exclude_set += word

    save()
    make_dict()
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
