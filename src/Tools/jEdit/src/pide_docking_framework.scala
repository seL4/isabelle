/*  Title:      Tools/jEdit/src/pide_docking_framework.scala
    Author:     Makarius

PIDE docking framework: "Original" with some add-ons.
*/

package isabelle.jedit


import isabelle._

import java.awt.event.{ActionListener, ActionEvent}
import javax.swing.{JPopupMenu, JMenuItem}

import org.gjt.sp.jedit.View
import org.gjt.sp.jedit.gui.{DockableWindowManagerProvider, DockableWindowFactory,
  DockableWindowManager, DockableWindowManagerImpl, DockableWindowContainer,
  FloatingWindowContainer, PanelWindowContainer}


class PIDE_Docking_Framework extends DockableWindowManagerProvider
{
  override def create(
    view: View,
    instance: DockableWindowFactory,
    config: View.ViewConfig): DockableWindowManager =
  new DockableWindowManagerImpl(view, instance, config)
  {
    override def createPopupMenu(
      container: DockableWindowContainer,
      dockable_name: String,
      clone: Boolean): JPopupMenu =
    {
      val menu = super.createPopupMenu(container, dockable_name, clone)

      val detach_operation: Option[() => Unit] =
        container match {
          case floating: FloatingWindowContainer =>
            val entry = Untyped.get(floating, "entry")
            val win = Untyped.get(entry, "win")
            win match {
              case dockable: Dockable => dockable.detach_operation
              case _ => None
            }

          case panel: PanelWindowContainer =>
            val entries =
              Untyped.get(panel, "dockables").asInstanceOf[java.util.List[AnyRef]].toArray
            val wins =
              (for {
                entry <- entries.iterator
                if Untyped.get(Untyped.get(entry, "factory"), "name") == dockable_name
                win = Untyped.get(entry, "win")
                if win != null
              } yield win).toList
            wins match {
              case List(dockable: Dockable) => dockable.detach_operation
              case _ => None
            }

          case _ => None
        }
      if (detach_operation.isDefined) {
        val detach_item = new JMenuItem("Detach")
        detach_item.addActionListener(new ActionListener {
          def actionPerformed(evt: ActionEvent) { detach_operation.get.apply() }
        })
        menu.add(detach_item)
      }

      menu
    }
  }
}
