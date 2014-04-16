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
import scala.collection.immutable.SortedMap

import org.gjt.sp.jedit.textarea.TextArea


object Spell_Checker
{
  /* words within text */

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

  def current_word(text_area: TextArea, rendering: Rendering, range: Text.Range)
    : Option[Text.Info[String]] =
  {
    for {
      spell_range <- rendering.spell_checker_point(range)
      text <- JEdit_Lib.try_get_text(text_area.getBuffer, spell_range)
      info <- marked_words(spell_range.start, text, info => info.range.overlaps(range)).headOption
    } yield info
  }


  /* dictionary declarations */

  class Dictionary private[Spell_Checker](val path: Path)
  {
    val lang = path.split_ext._1.base.implode
    val user_path = Path.explode("$ISABELLE_HOME_USER/dictionaries") + Path.basic(lang)
    override def toString: String = lang
  }

  private object Decl
  {
    def apply(name: String, include: Boolean): String =
      if (include) name else "-" + name

    def unapply(decl: String): Option[(String, Boolean)] =
    {
      val decl1 = decl.trim
      if (decl1 == "" || decl1.startsWith("#")) None
      else
        Library.try_unprefix("-", decl1.trim) match {
          case None => Some((decl1, true))
          case Some(decl2) => Some((decl2, false))
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

  private sealed case class Update(include: Boolean, permanent: Boolean)
}


class Spell_Checker private(dictionary: Spell_Checker.Dictionary)
{
  override def toString: String = dictionary.toString

  private var dict = new Object
  private var updates = SortedMap.empty[String, Spell_Checker.Update]

  private def included_iterator(): Iterator[String] =
    for {
      (word, upd) <- updates.iterator
      if upd.include
    } yield word

  private def excluded(word: String): Boolean =
    updates.get(word) match {
      case Some(upd) => !upd.include
      case None => false
    }

  private def load()
  {
    val main_dictionary = split_lines(File.read_gzip(dictionary.path))

    val permanent_updates =
      if (dictionary.user_path.is_file)
        for {
          Spell_Checker.Decl(word, include) <- split_lines(File.read(dictionary.user_path))
        } yield (word, Spell_Checker.Update(include, true))
      else Nil

    updates =
      updates -- (for ((name, upd) <- updates.iterator; if upd.permanent) yield name) ++
        permanent_updates

    val factory_class = Class.forName("com.inet.jortho.DictionaryFactory")
    val factory_cons = factory_class.getConstructor()
    factory_cons.setAccessible(true)
    val factory = factory_cons.newInstance()

    val add = factory_class.getDeclaredMethod("add", classOf[String])
    add.setAccessible(true)

    for {
      word <- main_dictionary.iterator ++ included_iterator()
      if !excluded(word)
    } add.invoke(factory, word)

    val create = factory_class.getDeclaredMethod("create")
    create.setAccessible(true)
    dict = create.invoke(factory)
  }
  load()

  private def save()
  {
    val permanent_decls =
      (for {
        (word, upd) <- updates.iterator
        if upd.permanent
      } yield Spell_Checker.Decl(word, upd.include)).toList

    if (!permanent_decls.isEmpty || dictionary.user_path.is_file) {
      val header = """# User updates for spell-checker dictionary
#
#   * each line contains at most one word
#   * extra blanks are ignored
#   * lines starting with "#" are stripped
#   * lines starting with "-" indicate excluded words
#
#:mode=text:encoding=UTF-8:

"""
      Isabelle_System.mkdirs(dictionary.user_path.expand.dir)
      File.write(dictionary.user_path, header + cat_lines(permanent_decls))
    }
  }

  def update(word: String, include: Boolean, permanent: Boolean)
  {
    updates += (word -> Spell_Checker.Update(include, permanent))

    if (include) {
      if (permanent) save()

      val m = dict.getClass.getDeclaredMethod("add", classOf[String])
      m.setAccessible(true)
      m.invoke(dict, word)
    }
    else { save(); load() }
  }

  def reset()
  {
    updates = SortedMap.empty
    load()
  }

  def reset_enabled(): Int =
    updates.valuesIterator.filter(upd => !upd.permanent).length

  def contains(word: String): Boolean =
  {
    val m = dict.getClass.getSuperclass.getDeclaredMethod("exist", classOf[String])
    m.setAccessible(true)
    m.invoke(dict, word).asInstanceOf[java.lang.Boolean].booleanValue
  }

  def check(word: String): Boolean =
    word match {
      case Word.Case(Word.Uppercase) => contains(Word.lowercase(word))
      case Word.Case(Word.Capitalized) =>
        contains(Word.lowercase(word)) || contains(Word.uppercase(word))
      case _ => contains(word)
    }

  def complete(word: String): List[String] =
    if (check(word)) Nil
    else {
      val m = dict.getClass.getSuperclass.getDeclaredMethod("searchSuggestions", classOf[String])
      m.setAccessible(true)
      m.invoke(dict, word).asInstanceOf[java.util.List[AnyRef]].toArray.toList.map(_.toString)
    }

  def complete_enabled(word: String): Boolean = !complete(word).isEmpty

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

