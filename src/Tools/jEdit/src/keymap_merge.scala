/*  Title:      Tools/jEdit/src/keymap_merge.scala
    Author:     Makarius

Merge of Isabelle/jEdit shortcuts wrt. jEdit keymap.
*/

package isabelle.jedit


import isabelle._

import java.awt.event.WindowEvent
import javax.swing.{WindowConstants, JDialog, JTable, JScrollPane}

import scala.collection.mutable
import scala.collection.JavaConversions
import scala.collection.immutable.SortedSet
import scala.swing.{FlowPanel, BorderPanel, Component, Button}
import scala.swing.event.ButtonClicked

import org.gjt.sp.jedit.{jEdit, View, GUIUtilities}
import org.jedit.keymap.{KeymapManager, Keymap}


object Keymap_Merge
{
  /* Isabelle/jEdit shortcuts */

  sealed case class Shortcut(action: String, key: String, alternative: Boolean)
  {
    def eq_action(that: Shortcut): Boolean = action == that.action

    val property: String = if (alternative) action + ".shortcut2" else action + ".shortcut"
    val label: String =
      GUIUtilities.prettifyMenuLabel(jEdit.getProperty(action + ".label", ""))
  }

  def additional_shortcuts(): List[Shortcut] =
  {
    val result = new mutable.ListBuffer[Shortcut]
    for (entry <- JavaConversions.mapAsScalaMap(jEdit.getProperties)) {
      entry match {
        case (a: String, b: String) if a.endsWith(".shortcut") =>
          val action = a.substring(0, a.length - 9)
          result += Shortcut(action, b, false)
        case (a: String, b: String) if a.endsWith(".shortcut2") =>
          val action = a.substring(0, a.length - 10)
          result += Shortcut(action, b, true)
        case _ =>
      }
    }
    result.toList
  }


  /* jEdit keymap */

  def current_keymap(): Keymap =
  {
    val manager = jEdit.getKeymapManager
    val name = jEdit.getProperty("keymap.current", KeymapManager.DEFAULT_KEYMAP_NAME)
    manager.getKeymap(name) match {
      case null => manager.getKeymap(KeymapManager.DEFAULT_KEYMAP_NAME)
      case keymap => keymap
    }
  }



  /** dialog **/

  def dialog(view: View)
  {
    GUI_Thread.require {}
    new Dialog(view)
  }

  private class Dialog(view: View) extends JDialog(view)
  {
    /* table */

    val shortcuts = additional_shortcuts()

    def get_label(action: String): String =
      shortcuts.collectFirst(
        { case s if s.action == action && s.label != "" => s.label }).getOrElse(action)

    def get_key(action: String, alternative: Boolean): String =
      shortcuts.collectFirst(
        { case s if s.action == action && s.alternative == alternative => s.key }).getOrElse("")

    val column_names: Array[AnyRef] =
      Array(jEdit.getProperty("options.shortcuts.name"),
        jEdit.getProperty("options.shortcuts.shortcut1"),
        jEdit.getProperty("options.shortcuts.shortcut2"))

    val table_rows: Array[Array[AnyRef]] =
      Library.distinct[Shortcut](shortcuts, _ eq_action _).sortBy(_.action).
        map(s => Array[AnyRef](s.label, get_key(s.action, false), get_key(s.action, true))).toArray

    val table = new JTable(table_rows, column_names)
    table.setRowHeight(GUIUtilities.defaultRowHeight())
    table.getTableHeader().setReorderingAllowed(false)  // FIXME !?

    val table_size = table.getPreferredSize()
    table_size.height = table_size.height min 200

    val table_scroller = new JScrollPane(table)
    table_scroller.setPreferredSize(table_size)


    /* buttons */

    val ok_button = new Button("OK") {
      reactions += { case ButtonClicked(_) => close() }  // FIXME
    }

    val cancel_button = new Button("Cancel") {
      reactions += { case ButtonClicked(_) => close() }  // FIXME
    }

    private def close()
    {
      setVisible(false)
      dispose()
    }


    /* layout */

    private val action_panel = new FlowPanel(FlowPanel.Alignment.Right)(ok_button, cancel_button)
    private val layout_panel = new BorderPanel
    layout_panel.layout(Component.wrap(table_scroller)) = BorderPanel.Position.Center
    layout_panel.layout(action_panel) = BorderPanel.Position.South

    setContentPane(layout_panel.peer)


    /* main */

    setDefaultCloseOperation(WindowConstants.DISPOSE_ON_CLOSE)

    setTitle("Isabelle/jEdit keymap changes")

    pack()
    setLocationRelativeTo(view)
    setVisible(true)
  }
}
