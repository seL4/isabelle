/*  Title:      Tools/jEdit/src/spell_checker.scala
    Author:     Makarius

Spell checker with completion, based on JOrtho (see
http://sourceforge.net/projects/jortho).
*/

package isabelle.jedit


import isabelle._

import java.lang.Class

import javax.swing.JMenuItem

import scala.collection.mutable
import scala.swing.ComboBox
import scala.annotation.tailrec
import scala.collection.immutable.SortedMap

import org.gjt.sp.jedit.menu.EnhancedMenuItem
import org.gjt.sp.jedit.{jEdit, Buffer}
import org.gjt.sp.jedit.textarea.{JEditTextArea, TextArea}


object Spell_Checker
{
  /** words within text **/

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



  /** completion **/

  def completion(text_area: TextArea, explicit: Boolean, rendering: Rendering)
      : Option[Completion.Result] =
  {
    for {
      spell_checker <- PIDE.spell_checker.get
      if explicit
      range = JEdit_Lib.before_caret_range(text_area, rendering)
      word <- current_word(text_area, rendering, range)
      words = spell_checker.complete(word.info)
      if words.nonEmpty
      descr = "(from dictionary " + quote(spell_checker.toString) + ")"
      items =
        words.map(w => Completion.Item(word.range, word.info, "", List(w, descr), w, 0, false))
    } yield Completion.Result(word.range, word.info, false, items)
  }



  /** context menu **/

  def context_menu(text_area: JEditTextArea, offset: Text.Offset): List[JMenuItem] =
  {
    val result =
      for {
        spell_checker <- PIDE.spell_checker.get
        doc_view <- PIDE.document_view(text_area)
        rendering = doc_view.get_rendering()
        range = JEdit_Lib.point_range(text_area.getBuffer, offset)
        Text.Info(_, word) <- current_word(text_area, rendering, range)
      } yield (spell_checker, word)

    result match {
      case Some((spell_checker, word)) =>

        val context = jEdit.getActionContext()
        def item(name: String): JMenuItem =
          new EnhancedMenuItem(context.getAction(name).getLabel, name, context)

        val complete_items =
          if (spell_checker.complete_enabled(word)) List(item("isabelle.complete-word"))
          else Nil

        val update_items =
          if (spell_checker.check(word))
            List(item("isabelle.exclude-word"), item("isabelle.exclude-word-permanently"))
          else
            List(item("isabelle.include-word"), item("isabelle.include-word-permanently"))

        val reset_items =
          spell_checker.reset_enabled() match {
            case 0 => Nil
            case n =>
              val name = "isabelle.reset-words"
              val label = context.getAction(name).getLabel
              List(new EnhancedMenuItem(label + " (" + n + ")", name, context))
          }

        complete_items ::: update_items ::: reset_items

      case None => Nil
    }
  }



  /** dictionary **/

  /* declarations */

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
    GUI_Thread.require {}

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
    component.tooltip = GUI.tooltip_lines(opt.print_default)
    component
  }


  /* create spell checker */

  def apply(dictionary: Dictionary): Spell_Checker = new Spell_Checker(dictionary)

  private sealed case class Update(include: Boolean, permanent: Boolean)
}


class Spell_Checker private(dictionary: Spell_Checker.Dictionary)
{
  override def toString: String = dictionary.toString


  /* main dictionary content */

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

    val add = Untyped.method(factory_class, "add", classOf[String])

    for {
      word <- main_dictionary.iterator ++ included_iterator()
      if !excluded(word)
    } add.invoke(factory, word)

    dict = Untyped.method(factory_class, "create").invoke(factory)
  }
  load()

  private def save()
  {
    val permanent_decls =
      (for {
        (word, upd) <- updates.iterator
        if upd.permanent
      } yield Spell_Checker.Decl(word, upd.include)).toList

    if (permanent_decls.nonEmpty || dictionary.user_path.is_file) {
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
      Untyped.method(dict.getClass, "add", classOf[String]).invoke(dict, word)
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


  /* check known words */

  def contains(word: String): Boolean =
    Untyped.method(dict.getClass.getSuperclass, "exist", classOf[String]).
      invoke(dict, word).asInstanceOf[java.lang.Boolean].booleanValue

  def check(word: String): Boolean =
    word match {
      case Word.Case(c) if c != Word.Lowercase =>
        contains(word) || contains(Word.lowercase(word))
      case _ =>
        contains(word)
    }

  def marked_words(base: Text.Offset, text: String): List[Text.Info[String]] =
    Spell_Checker.marked_words(base, text, info => !check(info.info))


  /* suggestions for unknown words */

  private def suggestions(word: String): Option[List[String]] =
  {
    val res =
      Untyped.method(dict.getClass.getSuperclass, "searchSuggestions", classOf[String]).
        invoke(dict, word).asInstanceOf[java.util.List[AnyRef]].toArray.toList.map(_.toString)
    if (res.isEmpty) None else Some(res)
  }

  def complete(word: String): List[String] =
    if (check(word)) Nil
    else {
      val word_case = Word.Case.unapply(word)
      def recover_case(s: String) =
        word_case match {
          case Some(c) => Word.Case(c, s)
          case None => s
        }
      val result =
        word_case match {
          case Some(c) if c != Word.Lowercase =>
            suggestions(word) orElse suggestions(Word.lowercase(word))
          case _ =>
            suggestions(word)
        }
      result.getOrElse(Nil).map(recover_case)
    }

  def complete_enabled(word: String): Boolean = complete(word).nonEmpty
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

