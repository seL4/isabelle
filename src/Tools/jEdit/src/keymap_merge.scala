/*  Title:      Tools/jEdit/src/keymap_merge.scala
    Author:     Makarius

Merge of Isabelle shortcuts vs. jEdit keymap.
*/

package isabelle.jedit


import isabelle._

import java.awt.event.WindowEvent
import javax.swing.{WindowConstants, JDialog, JTable, JScrollPane}

import scala.collection.JavaConversions
import scala.swing.{FlowPanel, BorderPanel, Component, Button}
import scala.swing.event.ButtonClicked

import org.gjt.sp.jedit.{jEdit, View, GUIUtilities}
import org.jedit.keymap.{KeymapManager, Keymap}


object Keymap_Merge
{
  /** shortcuts **/

  private def is_shortcut(property: String): Boolean =
    (property.endsWith(".shortcut") || property.endsWith(".shortcut2")) &&
    !property.startsWith("options.shortcuts.")

  class Shortcut(val property: String, val binding: String)
  {
    override def toString: String = property + "=" + binding

    def primary: Boolean = property.endsWith(".shortcut")

    val action: String =
      Library.try_unsuffix(".shortcut", property) orElse
      Library.try_unsuffix(".shortcut2", property) getOrElse
      error("Bad shortcut property: " + quote(property))

    val label: String =
      GUIUtilities.prettifyMenuLabel(jEdit.getProperty(action + ".label", ""))


    /* ignore wrt. keymaps */

    private def prop_ignore: String = property + ".ignore"

    def ignored_keymaps(): List[String] =
      Library.space_explode(',', jEdit.getProperty(prop_ignore, ""))

    def is_ignored(keymap_name: String): Boolean =
      ignored_keymaps().contains(keymap_name)

    def update_ignored(keymap_name: String, ignore: Boolean)
    {
      val keymaps1 =
        if (ignore) Library.insert(keymap_name)(ignored_keymaps()).sorted
        else Library.remove(keymap_name)(ignored_keymaps())

      if (keymaps1.isEmpty) jEdit.resetProperty(prop_ignore)
      else jEdit.setProperty(prop_ignore, keymaps1.mkString(","))
    }
  }

  def convert_properties(props: java.util.Properties): List[Shortcut] =
    if (props == null) Nil
    else {
      var result = List.empty[Shortcut]
      for (entry <- JavaConversions.mapAsScalaMap(props)) {
        entry match {
          case (a: String, b: String) if is_shortcut(a) =>
            result ::= new Shortcut(a, b)
          case _ =>
        }
      }
      result.sortBy(_.property)
    }


  /* keymap */

  def get_keymap(): (String, Keymap) =
  {
    val manager = jEdit.getKeymapManager
    val keymap_name = jEdit.getProperty("keymap.current", KeymapManager.DEFAULT_KEYMAP_NAME)
    val keymap =
      manager.getKeymap(keymap_name) match {
        case null => manager.getKeymap(KeymapManager.DEFAULT_KEYMAP_NAME)
        case keymap => keymap
      }
    (keymap_name, keymap)
  }

  def change_keymap(keymap: Keymap, entry: (Shortcut, List[Shortcut]))
  {
    val (shortcut, conflicts) = entry
    conflicts.foreach(s => keymap.setShortcut(s.property, ""))
    keymap.setShortcut(shortcut.property, shortcut.binding)
  }

  def shortcut_conflicts(show_all: Boolean = false): List[(Shortcut, List[Shortcut])] =
  {
    val (keymap_name, keymap) = get_keymap()
    val keymap_shortcuts =
      if (keymap == null) Nil
      else convert_properties(Untyped.get[java.util.Properties](keymap, "props"))

    for {
      s <- convert_properties(jEdit.getProperties)
      if show_all || !s.is_ignored(keymap_name)
    }
    yield {
      val conflicts =
        keymap_shortcuts.filter(s1 =>
          s.property == s1.property && s.binding != s1.binding ||
          s.property != s1.property && s.binding == s1.binding)
      (s, conflicts)
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

    val shortcuts = List.empty[Shortcut]

    def get_label(action: String): String =
      shortcuts.collectFirst(
        { case s if s.action == action && s.label != "" => s.label }).getOrElse(action)

    def get_binding(action: String, primary: Boolean): String =
      shortcuts.collectFirst(
        { case s if s.action == action && s.primary == primary => s.binding }).getOrElse("")

    val column_names: Array[AnyRef] =
      Array(jEdit.getProperty("options.shortcuts.name"),
        jEdit.getProperty("options.shortcuts.shortcut1"),
        jEdit.getProperty("options.shortcuts.shortcut2"))

    val table_rows: Array[Array[AnyRef]] =
      shortcuts.map(s =>
        Array[AnyRef](s.label, get_binding(s.action, true), get_binding(s.action, false))).toArray

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
