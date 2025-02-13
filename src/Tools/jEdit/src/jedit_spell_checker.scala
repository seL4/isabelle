/*  Title:      Tools/jEdit/src/jedit_spell_checker.scala
    Author:     Makarius

Specific spell-checker support for Isabelle/jEdit.
*/

package isabelle.jedit


import isabelle._

import javax.swing.JMenuItem

import org.gjt.sp.jedit.menu.EnhancedMenuItem
import org.gjt.sp.jedit.jEdit
import org.gjt.sp.jedit.textarea.JEditTextArea


object JEdit_Spell_Checker {
  /* completion */

  def completion(
    rendering: JEdit_Rendering,
    explicit: Boolean,
    caret: Text.Offset
  ): Option[Completion.Result] = {
    PIDE.plugin.spell_checker.get match {
      case Some(spell_checker) if explicit =>
        spell_checker.completion(rendering, caret)
      case _ => None
    }
  }


  /* context menu */

  def context_menu(text_area: JEditTextArea, offset: Text.Offset): List[JMenuItem] = {
    val result =
      for {
        spell_checker <- PIDE.plugin.spell_checker.get
        rendering <- Document_View.get_rendering(text_area)
        range = JEdit_Lib.point_range(text_area.getBuffer, offset)
        Text.Info(_, word) <- Spell_Checker.current_word(rendering, range)
      } yield (spell_checker, word)

    result match {
      case Some((spell_checker, word)) =>

        val context = jEdit.getActionContext()
        def item(name: String): JMenuItem =
          new EnhancedMenuItem(context.getAction(name).getLabel, name, context)

        val complete_items =
          if (spell_checker.complete(word).nonEmpty) List(item("isabelle.complete-word"))
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


  /* dictionaries */

  def dictionaries_selector(): JEdit_Options.Entry = {
    GUI_Thread.require {}

    val option_name = "spell_checker_dictionary"
    val opt = PIDE.options.value.check_name(option_name)

    new GUI.Selector(Spell_Checker.dictionaries.map(GUI.Selector.item)) with JEdit_Options.Entry {
      name = option_name
      tooltip = GUI.tooltip_lines(opt.print_default)

      override val title: String = opt.title_jedit
      override def load(): Unit = {
        val lang = PIDE.options.string(option_name)
        for (dict <- Spell_Checker.get_dictionary(lang)) selection.item = GUI.Selector.item(dict)
      }
      override def save(): Unit =
        for (dict <- selection_value) PIDE.options.string(option_name) = dict.lang

      load()
    }
  }
}
