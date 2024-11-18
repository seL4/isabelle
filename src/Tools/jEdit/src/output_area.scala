/*  Title:      Tools/jEdit/src/output_area.scala
    Author:     Makarius

GUI component for structured output.
*/

package isabelle.jedit


import isabelle._

import java.awt.Dimension
import java.awt.event.{ComponentEvent, ComponentAdapter, FocusAdapter, FocusEvent,
  MouseEvent, MouseAdapter}
import javax.swing.JComponent

import scala.util.matching.Regex
import scala.swing.{Component, ScrollPane, SplitPane, Orientation}
import scala.swing.event.ButtonClicked

import org.gjt.sp.jedit.View


class Output_Area(view: View, root_name: String = "Overview") {
  output_area =>

  GUI_Thread.require {}


  /* tree view */

  val tree: Tree_View =
    new Tree_View(root = Tree_View.Node(root_name), single_selection_mode = true)


  /* text area */

  val pretty_text_area: Pretty_Text_Area =
    new Pretty_Text_Area(view) {
      override def handle_search(search: Pretty_Text_Area.Search_Results): Unit =
        output_area.handle_search(search)
    }

  def handle_search(search: Pretty_Text_Area.Search_Results): Unit = ()
  def handle_resize(): Unit = pretty_text_area.zoom()
  def handle_update(): Unit = ()

  lazy val delay_resize: Delay =
    Delay.first(PIDE.session.update_delay, gui = true) { handle_resize() }


  /* handle events */

  def handle_focus(): Unit = ()

  private lazy val component_listener =
    new ComponentAdapter {
      override def componentResized(e: ComponentEvent): Unit = delay_resize.invoke()
      override def componentShown(e: ComponentEvent): Unit = delay_resize.invoke()
    }

  private lazy val focus_listener =
    new FocusAdapter {
      override def focusGained(e: FocusEvent): Unit = handle_focus()
    }

  private lazy val mouse_listener =
    new MouseAdapter {
      override def mouseClicked(e: MouseEvent): Unit = {
        if (!e.isConsumed()) {
          val click = tree.getPathForLocation(e.getX, e.getY)
          if (click != null && e.getClickCount == 1) {
            e.consume()
            handle_focus()
          }
        }
      }
    }


  /* GUI components */

  lazy val tree_pane: Component = {
    val scroll_pane: ScrollPane = new ScrollPane(Component.wrap(tree))
    scroll_pane.horizontalScrollBarPolicy = ScrollPane.BarPolicy.Always
    scroll_pane.verticalScrollBarPolicy = ScrollPane.BarPolicy.Always
    scroll_pane.minimumSize = new Dimension(200, 100)
    scroll_pane
  }

  lazy val text_pane: Component = Component.wrap(pretty_text_area)

  lazy val split_pane: SplitPane =
    new SplitPane(Orientation.Vertical) {
      oneTouchExpandable = true
      leftComponent = tree_pane
      rightComponent = text_pane
    }

  def init_gui(parent: JComponent, split: Boolean = false): Unit = {
    parent.addComponentListener(component_listener)
    parent.addFocusListener(focus_listener)
    tree.addMouseListener(mouse_listener)
    parent match {
      case dockable: Dockable => dockable.set_content(if (split) split_pane else text_pane)
      case _ =>
    }
  }

  def init(): Unit = handle_update()

  def exit(): Unit = delay_resize.revoke()
}
