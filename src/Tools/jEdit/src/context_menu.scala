/*  Title:      Tools/jEdit/src/context_menu.scala
    Author:     Makarius

Common context menu for Isabelle/jEdit.
*/

package isabelle.jedit


import isabelle._


import java.awt.event.MouseEvent
import javax.swing.JMenuItem

import org.gjt.sp.jedit.menu.EnhancedMenuItem
import org.gjt.sp.jedit.gui.DynamicContextMenuService
import org.gjt.sp.jedit.jEdit
import org.gjt.sp.jedit.textarea.JEditTextArea


class Context_Menu extends DynamicContextMenuService
{
  /* spell checker menu */

  private def action_item(name: String): JMenuItem =
  {
    val context = jEdit.getActionContext()
    new EnhancedMenuItem(context.getAction(name).getLabel, name, context)
  }

  private def spell_checker_menu(text_area: JEditTextArea, offset: Text.Offset): List[JMenuItem] =
  {
    val result =
      for {
        spell_checker <- PIDE.spell_checker.get
        doc_view <- PIDE.document_view(text_area)
        rendering = doc_view.get_rendering()
        range = JEdit_Lib.point_range(text_area.getBuffer, offset)
        Text.Info(_, word) <- Spell_Checker.current_word(text_area, rendering, range)
      } yield spell_checker.check(word)

    result match {
      case Some(false) =>
        List(
          action_item("isabelle.complete-word"),
          action_item("isabelle.include-word"),
          action_item("isabelle.include-word-permanently"),
          action_item("isabelle.reset-words"))
      case Some(true) =>
        List(
          action_item("isabelle.exclude-word"),
          action_item("isabelle.exclude-word-permanently"),
          action_item("isabelle.reset-words"))
      case None => Nil
    }
  }


  /* menu service */

  def createMenu(text_area: JEditTextArea, evt: MouseEvent): Array[JMenuItem] =
  {
    if (evt != null && evt.getSource == text_area.getPainter) {
      val offset = text_area.xyToOffset(evt.getX, evt.getY)
      if (offset >= 0) {
        val items = spell_checker_menu(text_area, offset)
        if (items.isEmpty) null else items.toArray
      }
      else null
    }
    else null
  }
}

