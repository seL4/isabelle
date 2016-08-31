/*  Title:      Tools/jEdit/src/keymap_merge.scala
    Author:     Makarius

Merge of Isabelle shortcuts vs. jEdit keymap.
*/

package isabelle.jedit


import isabelle._

import java.lang.Class
import java.awt.Dimension
import java.awt.event.WindowEvent
import javax.swing.{WindowConstants, JDialog, JTable, JScrollPane}
import javax.swing.table.AbstractTableModel

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

  def get_shortcut_conflicts(keymap: Keymap): List[(Shortcut, List[Shortcut])] =
  {
    val keymap_shortcuts =
      if (keymap == null) Nil
      else convert_properties(Untyped.get[java.util.Properties](keymap, "props"))

    for (s <- convert_properties(jEdit.getProperties)) yield {
      val conflicts =
        keymap_shortcuts.filter(s1 =>
          s.property == s1.property && s.binding != s1.binding ||
          s.property != s1.property && s.binding == s1.binding)
      (s, conflicts)
    }
  }



  /** table model **/

  private sealed case class Table_Entry(shortcut: Shortcut, head: Boolean)
  {
    override def toString: String =
      if (head) "<html>" + HTML.output(shortcut.toString) + "</html>"
      else
        "<html><font style='color: #B22222;'>" +
          HTML.output(" -- " + shortcut.toString) +
        "</font></html>"
  }

  private class Table_Model(entries: List[Table_Entry]) extends AbstractTableModel
  {
    private val entries_count = entries.length
    private def get_entry(row: Int): Option[Table_Entry] =
      if (0 <= row && row <= entries_count) Some(entries(row)) else None

    private val ignored = Synchronized(Set.empty[Shortcut])

    def select(row: Int, b: Boolean)
    {
      for (entry <- get_entry(row) if entry.head) {
        ignored.change(set => if (b) set - entry.shortcut else set + entry.shortcut)
      }
    }

    def selected_status(row: Int): Option[Boolean] =
      get_entry(row) match {
        case Some(entry) if entry.head => Some(!ignored.value.contains(entry.shortcut))
        case _ => None
      }

    override def getColumnCount: Int = 2

    override def getColumnClass(i: Int): Class[_ <: Object] =
      if (i == 0) classOf[java.lang.Boolean]
      else classOf[java.lang.Object]

    override def getColumnName(i: Int): String =
      if (i == 0) " " else if (i == 1) "Keyboard shortcut" else "???"

    override def getRowCount: Int = entries_count

    override def getValueAt(row: Int, column: Int): AnyRef =
    {
      get_entry(row) match {
        case Some(entry) if column == 0 =>
          selected_status(row) match {
            case None => null
            case Some(true) => java.lang.Boolean.TRUE
            case Some(false) => java.lang.Boolean.FALSE
          }
        case Some(entry) if column == 1 => entry
        case _ => null
      }
    }
  }



  /** dialog **/

  def check_dialog(view: View)
  {
    GUI_Thread.require {}

    val (keymap_name, keymap) = get_keymap()
    val shortcut_conflicts = get_shortcut_conflicts(keymap)

    val pending_conflicts =
      shortcut_conflicts.filter({ case (s, cs) => !s.is_ignored(keymap_name) && cs.nonEmpty })
    if (pending_conflicts.nonEmpty) new Dialog(view, pending_conflicts)
    // FIXME else silent change
  }

  private class Dialog(view: View, shortcut_conflicts: List[(Shortcut, List[Shortcut])])
    extends JDialog(view)
  {
    /* table */

    val table_entries =
      for {
        (shortcut, conflicts) <- shortcut_conflicts
        entry <- Table_Entry(shortcut, true) :: conflicts.map(Table_Entry(_, false))
      } yield entry

    val table_model = new Table_Model(table_entries)

    val table = new JTable(table_model)
    table.setShowGrid(false)
    table.setIntercellSpacing(new Dimension(0, 0))
    table.setRowHeight(GUIUtilities.defaultRowHeight() + 2)
    table.setPreferredScrollableViewportSize(new Dimension(500, 300))
    table.getTableHeader.setReorderingAllowed(false)

		val col0 = table.getColumnModel.getColumn(0)
		val col1 = table.getColumnModel.getColumn(1)

		col0.setPreferredWidth(30)
		col0.setMinWidth(30)
		col0.setMaxWidth(30)
		col0.setResizable(false)

		col1.setPreferredWidth(300)

    val table_scroller = new JScrollPane(table)
		table_scroller.getViewport.setBackground(table.getBackground)
		table_scroller.setPreferredSize(new Dimension(400, 400))


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
