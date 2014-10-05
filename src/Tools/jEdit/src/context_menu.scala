/*  Title:      Tools/jEdit/src/context_menu.scala
    Author:     Makarius

Common context menu for Isabelle/jEdit.
*/

package isabelle.jedit


import isabelle._


import java.awt.event.{ActionListener, ActionEvent, MouseEvent}
import javax.swing.{JMenu, JMenuItem}

import org.gjt.sp.jedit.menu.EnhancedMenuItem
import org.gjt.sp.jedit.gui.DynamicContextMenuService
import org.gjt.sp.jedit.{jEdit, Buffer}
import org.gjt.sp.jedit.textarea.{JEditTextArea, TextArea}


class Context_Menu extends DynamicContextMenuService
{
  /* spell checker menu */

  private def spell_checker_menu(text_area: JEditTextArea, offset: Text.Offset): List[JMenuItem] =
  {
    val result =
      for {
        spell_checker <- PIDE.spell_checker.get
        doc_view <- PIDE.document_view(text_area)
        rendering = doc_view.get_rendering()
        range = JEdit_Lib.point_range(text_area.getBuffer, offset)
        Text.Info(_, word) <- Spell_Checker.current_word(text_area, rendering, range)
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


  /* bibtex menu */

  def bibtex_menu(text_area0: JEditTextArea): List[JMenuItem] =
  {
    text_area0 match {
      case text_area: TextArea =>
        text_area.getBuffer match {
          case buffer: Buffer
          if (Isabelle.is_bibtex(buffer) && buffer.isEditable) =>
            val menu = new JMenu("BibTeX entries")
            for (entry <- Bibtex.entries) {
              val item = new JMenuItem(entry.kind)
              item.addActionListener(new ActionListener {
                def actionPerformed(evt: ActionEvent): Unit =
                  Isabelle.insert_line_padding(text_area, entry.template)
              })
              menu.add(item)
            }
            List(menu)
          case _ => Nil
        }
      case _ => Nil
    }
  }


  /* menu service */

  def createMenu(text_area: JEditTextArea, evt: MouseEvent): Array[JMenuItem] =
  {
    PIDE.dismissed_popups(text_area.getView)

    val items1 =
      if (evt != null && evt.getSource == text_area.getPainter) {
        val offset = text_area.xyToOffset(evt.getX, evt.getY)
        if (offset >= 0) spell_checker_menu(text_area, offset)
        else Nil
      }
      else Nil

    val items2 = bibtex_menu(text_area)

    val items = items1 ::: items2
    if (items.isEmpty) null else items.toArray
  }
}

