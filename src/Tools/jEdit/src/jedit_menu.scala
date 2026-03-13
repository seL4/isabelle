/*  Title:      Tools/jEdit/src/jedit_menu.scala
    Author:     Makarius

Systematic modification of jEdit menus.
*/

package isabelle.jedit


import isabelle._

import org.gjt.sp.jedit.jEdit


object JEdit_Menu {
  sealed case class Entry(
    parent: JEdit_Property,
    hook: String,
    items: List[String],
    negate: Boolean = false
  ) {
    private def ins(): Unit = parent.load().insert_after(hook, items).save()
    private def rem(): Unit = parent.load().remove(items).save()
    def update(remove: Boolean = false): Unit = if (remove == negate) ins() else rem()
  }

  class Provider(val order: Int, val entries: Entry*) extends Isabelle_System.Service
  lazy val all_entries: List[Entry] =
    Isabelle_System.make_services(classOf[Provider]).sortBy(_.order).flatMap(_.entries)

  private def update(remove: Boolean = false): Unit = GUI_Thread.require {
    if (jEdit.getActiveView != null) {
      for (entry <- all_entries) entry.update(remove = remove)
      GUI_Thread.later { jEdit.propertiesChanged }
    }
  }

  def init(): Unit = update()
  def exit(): Unit = update(remove = true)
}

class Isabelle_Menu_Provider extends JEdit_Menu.Provider(Int.MinValue,
  JEdit_Menu.Entry(JEdit_Property.menu_bar, "plugins", List("isabelle-menu")),
  JEdit_Menu.Entry(JEdit_Property.file_menu, "reload-all",
    List("isabelle.recode-plain", "isabelle.recode-symbols")),
  JEdit_Menu.Entry(JEdit_Property.options_menu, "plugin-options", List("isabelle.options")),
  JEdit_Menu.Entry(JEdit_Property.help_menu, JEdit_Property.END,
    List("tip-of-the-day"), negate = true),
  JEdit_Menu.Entry(JEdit_Property.help_menu, JEdit_Property.END,
    List("isabelle-documentation"))
)
