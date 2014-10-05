/*  Title:      Tools/jEdit/src/context_menu.scala
    Author:     Makarius

Common context menu for Isabelle/jEdit.
*/

package isabelle.jedit


import isabelle._


import java.awt.event.MouseEvent

import javax.swing.JMenuItem

import org.gjt.sp.jedit.gui.DynamicContextMenuService
import org.gjt.sp.jedit.textarea.JEditTextArea


class Context_Menu extends DynamicContextMenuService
{
  def createMenu(text_area: JEditTextArea, evt: MouseEvent): Array[JMenuItem] =
  {
    PIDE.dismissed_popups(text_area.getView)

    val items1 =
      if (evt != null && evt.getSource == text_area.getPainter) {
        val offset = text_area.xyToOffset(evt.getX, evt.getY)
        if (offset >= 0) Spell_Checker.context_menu(text_area, offset)
        else Nil
      }
      else Nil

    val items2 = Bibtex_JEdit.context_menu(text_area)

    val items = items1 ::: items2
    if (items.isEmpty) null else items.toArray
  }
}

