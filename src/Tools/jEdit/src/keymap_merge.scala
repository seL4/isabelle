/*  Title:      Tools/jEdit/src/keymap_merge.scala
    Author:     Makarius

Merge of Isabelle shortcuts vs. jEdit keymap.
*/

package isabelle.jedit


import isabelle._

import java.util.{Properties => JProperties}
import java.awt.{Color, Dimension, BorderLayout}
import javax.swing.{JPanel, JTable, JScrollPane, JOptionPane}
import javax.swing.table.AbstractTableModel

import scala.jdk.CollectionConverters._

import org.gjt.sp.jedit.{jEdit, View}
import org.gjt.sp.util.GenericGUIUtilities
import org.jedit.keymap.{KeymapManager, Keymap}


object Keymap_Merge
{
  /** shortcuts **/

  private def is_shortcut(property: String): Boolean =
    (property.endsWith(".shortcut") || property.endsWith(".shortcut2")) &&
    !property.startsWith("options.shortcuts.")

  class Shortcut(val property: String, val binding: String)
  {
    override def toString: String = Properties.Eq(property, binding)

    def primary: Boolean = property.endsWith(".shortcut")

    val action: String =
      Library.try_unsuffix(".shortcut", property) orElse
      Library.try_unsuffix(".shortcut2", property) getOrElse
      error("Bad shortcut property: " + quote(property))

    val label: String =
      GenericGUIUtilities.prettifyMenuLabel(jEdit.getProperty(action + ".label", ""))


    /* ignore wrt. keymap */

    private def prop_ignore: String = property + ".ignore"

    def ignored_keymaps(): List[String] =
      space_explode(',', jEdit.getProperty(prop_ignore, ""))

    def is_ignored(keymap_name: String): Boolean =
      ignored_keymaps().contains(keymap_name)

    def ignore(keymap_name: String): Unit =
      jEdit.setProperty(prop_ignore,
        Library.insert(keymap_name)(ignored_keymaps()).sorted.mkString(","))

    def set(keymap: Keymap): Unit = keymap.setShortcut(property, binding)
    def reset(keymap: Keymap): Unit = keymap.setShortcut(property, null)
  }


  /* content wrt. keymap */

  def convert_properties(props: JProperties): List[Shortcut] =
    if (props == null) Nil
    else {
      var result = List.empty[Shortcut]
      for (entry <- props.asScala) {
        entry match {
          case (a: String, b: String) if is_shortcut(a) =>
            result ::= new Shortcut(a, b)
          case _ =>
        }
      }
      result.sortBy(_.property)
    }

  def get_shortcut_conflicts(keymap_name: String, keymap: Keymap): List[(Shortcut, List[Shortcut])] =
  {
    val keymap_shortcuts =
      if (keymap == null) Nil
      else convert_properties(Untyped.get[JProperties](keymap, "props"))

    for (s <- convert_properties(jEdit.getProperties) if !s.is_ignored(keymap_name)) yield {
      val conflicts =
        keymap_shortcuts.filter(s1 =>
          s.property == s1.property && s.binding != s1.binding ||
          s.property != s1.property && s.binding == s1.binding && s1.binding != "")
      (s, conflicts)
    }
  }



  /** table **/

  private def conflict_color: Color =
    PIDE.options.color_value("error_color")

  private sealed case class Table_Entry(shortcut: Shortcut, head: Option[Int], tail: List[Int])
  {
    override def toString: String =
      if (head.isEmpty) "<html>" + HTML.output(shortcut.toString) + "</html>"
      else
        "<html><font style='color: #" + Color_Value.print(conflict_color) + ";'>" +
          HTML.output("--- " + shortcut.toString) +
        "</font></html>"
  }

  private class Table_Model(entries: List[Table_Entry]) extends AbstractTableModel
  {
    private val entries_count = entries.length
    private def has_entry(row: Int): Boolean = 0 <= row && row <= entries_count
    private def get_entry(row: Int): Option[Table_Entry] =
      if (has_entry(row)) Some(entries(row)) else None

    private val selected =
      Synchronized[Set[Int]](
        (for ((e, i) <- entries.iterator.zipWithIndex if e.head.isEmpty) yield i).toSet)

    private def is_selected(row: Int): Boolean =
      selected.value.contains(row)

    private def select(head: Int, tail: List[Int], b: Boolean): Unit =
      selected.change(set => if (b) set + head -- tail else set - head ++ tail)

    def apply(keymap_name: String, keymap: Keymap): Unit =
    {
      GUI_Thread.require {}

      for ((entry, row) <- entries.iterator.zipWithIndex if entry.head.isEmpty) {
        val b = is_selected(row)
        if (b) {
          entry.tail.foreach(i => entries(i).shortcut.reset(keymap))
          entry.shortcut.set(keymap)
        }
        else
          entry.shortcut.ignore(keymap_name)
      }
    }

    override def getColumnCount: Int = 2

    override def getColumnClass(i: Int): Class[_ <: Object] =
      if (i == 0) classOf[java.lang.Boolean] else classOf[Object]

    override def getColumnName(i: Int): String =
      if (i == 0) " " else if (i == 1) "Keyboard shortcut" else "???"

    override def getRowCount: Int = entries_count

    override def getValueAt(row: Int, column: Int): AnyRef =
    {
      get_entry(row) match {
        case Some(entry) if column == 0 => java.lang.Boolean.valueOf(is_selected(row))
        case Some(entry) if column == 1 => entry
        case _ => null
      }
    }

    override def isCellEditable(row: Int, column: Int): Boolean =
      has_entry(row) && column == 0

    override def setValueAt(value: AnyRef, row: Int, column: Int): Unit =
    {
      value match {
        case obj: java.lang.Boolean if has_entry(row) && column == 0 =>
          val b = obj.booleanValue
          val entry = entries(row)
          entry.head match {
            case None => select(row, entry.tail, b)
            case Some(head_row) =>
              val head_entry = entries(head_row)
              select(head_row, head_entry.tail, !b)
          }
          GUI_Thread.later { fireTableDataChanged() }
        case _ =>
      }
    }
  }

  private class Table(table_model: Table_Model) extends JPanel(new BorderLayout)
  {
    private val cell_size = GenericGUIUtilities.defaultTableCellSize()
    private val table_size = new Dimension(cell_size.width * 2, cell_size.height * 15)

    val table = new JTable(table_model)
    table.setShowGrid(false)
    table.setIntercellSpacing(new Dimension(0, 0))
    table.setRowHeight(cell_size.height + 2)
    table.setPreferredScrollableViewportSize(table_size)
    table.setFillsViewportHeight(true)
    table.getTableHeader.setReorderingAllowed(false)

		table.getColumnModel.getColumn(0).setPreferredWidth(30)
		table.getColumnModel.getColumn(0).setMinWidth(30)
		table.getColumnModel.getColumn(0).setMaxWidth(30)
		table.getColumnModel.getColumn(0).setResizable(false)
		table.getColumnModel.getColumn(1).setPreferredWidth(table_size.width - 30)

    val scroller = new JScrollPane(table)
		scroller.getViewport.setBackground(table.getBackground)
		scroller.setPreferredSize(table_size)

    add(scroller, BorderLayout.CENTER)
  }



  /** check with optional dialog **/

  def check_dialog(view: View): Unit =
  {
    GUI_Thread.require {}

    val keymap_manager = jEdit.getKeymapManager
    val keymap_name = jEdit.getProperty("keymap.current", KeymapManager.DEFAULT_KEYMAP_NAME)
    val keymap =
      keymap_manager.getKeymap(keymap_name) match {
        case null => keymap_manager.getKeymap(KeymapManager.DEFAULT_KEYMAP_NAME)
        case keymap => keymap
      }

    val all_shortcut_conflicts = get_shortcut_conflicts(keymap_name, keymap)
    val no_shortcut_conflicts = for ((s, cs) <- all_shortcut_conflicts if cs.isEmpty) yield s
    val shortcut_conflicts = all_shortcut_conflicts.filter(_._2.nonEmpty)

    val table_entries =
      for {
        ((shortcut, conflicts), i) <- shortcut_conflicts zip
          shortcut_conflicts.scanLeft(0)({ case (i, (_, cs)) => i + 1 + cs.length })
        entry <-
          Table_Entry(shortcut, None, ((i + 1) to (i + conflicts.length)).toList) ::
          conflicts.map(Table_Entry(_, Some(i), Nil))
      } yield entry

    val table_model = new Table_Model(table_entries)

    if (table_entries.nonEmpty &&
        GUI.confirm_dialog(view,
          "Pending Isabelle/jEdit keymap changes",
          JOptionPane.OK_CANCEL_OPTION,
          "The following Isabelle keymap changes are in conflict with the current",
          "jEdit keymap " + quote(keymap_name) + ":",
          new Table(table_model),
          "Selected shortcuts will be applied, unselected changes will be ignored.",
          "Results are stored in $JEDIT_SETTINGS/properties and $JEDIT_SETTINGS/keymaps/.") == 0)
    { table_model.apply(keymap_name, keymap) }

    no_shortcut_conflicts.foreach(_.set(keymap))

    keymap.save()
    jEdit.saveSettings()
    jEdit.propertiesChanged()
  }
}
