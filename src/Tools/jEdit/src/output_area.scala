/*  Title:      Tools/jEdit/src/output_area.scala
    Author:     Makarius

GUI component for structured output.
*/

package isabelle.jedit


import isabelle._

import java.awt.Dimension
import java.awt.event.{ComponentEvent, ComponentAdapter, FocusAdapter, FocusEvent,
  HierarchyListener, HierarchyEvent, KeyEvent, KeyAdapter, MouseEvent, MouseAdapter}
import javax.swing.{JComponent, JButton}
import javax.swing.plaf.basic.BasicSplitPaneUI
import javax.swing.tree.TreePath

import scala.swing.{Component, ScrollPane, SplitPane, Orientation}

import org.gjt.sp.jedit.View


class Output_Area(view: View, root_name: String = Pretty_Text_Area.search_title()) {
  output_area =>

  GUI_Thread.require {}


  /* tree view */

  val tree_cell_renderer: Tree_View.Cell_Renderer = new Tree_View.Cell_Renderer

  val tree: Tree_View =
    new Tree_View(root = Tree_View.Node(root_name), single_selection_mode = true)

  private var search_activated = false

  def handle_search(search: Pretty_Text_Area.Search_Results): Unit = {
    if (!search_activated && search.pattern.isDefined) {
      search_activated = true
      delay_shown.invoke()
    }
    tree.init_model {
      tree.root.setUserObject(Pretty_Text_Area.search_title(lines = search.length))
      for (result <- search.results) tree.root.add(Tree_View.Node(result))
    }
    tree.revalidate()
  }

  def handle_tree_selection(path: TreePath = tree.getSelectionPath): Unit =
    for (result <- tree.get_selection(path, { case x: Pretty_Text_Area.Search_Result => x })) {
      pretty_text_area.setCaretPosition(result.line_range.start)
      JEdit_Lib.scroll_to_caret(pretty_text_area)
    }


  /* text area */

  val pretty_text_area: Pretty_Text_Area =
    new Pretty_Text_Area(view) {
      override def handle_search(search: Pretty_Text_Area.Search_Results): Unit =
        output_area.handle_search(search)
    }

  def handle_resize(): Unit = pretty_text_area.zoom()
  def handle_update(): Unit = ()

  lazy val delay_resize: Delay =
    Delay.first(PIDE.session.update_delay, gui = true) { handle_resize() }


  /* handle events */

  def handle_focus(): Unit = ()
  def handle_shown(): Unit = ()

  lazy val delay_shown: Delay =
    Delay.first(PIDE.session.input_delay, gui = true) { handle_shown() }

  private lazy val hierarchy_listener =
    new HierarchyListener {
      override def hierarchyChanged(e: HierarchyEvent): Unit = {
        val displayed =
          (e.getChangeFlags & HierarchyEvent.DISPLAYABILITY_CHANGED) != 0 &&
            e.getComponent.isDisplayable
        val shown =
          (e.getChangeFlags & HierarchyEvent.SHOWING_CHANGED) != 0 &&
            e.getComponent.isShowing
        if (displayed || shown) delay_shown.invoke()
      }
    }

  private lazy val component_listener =
    new ComponentAdapter {
      override def componentResized(e: ComponentEvent): Unit = delay_resize.invoke()
      override def componentShown(e: ComponentEvent): Unit = delay_resize.invoke()
    }

  private lazy val focus_listener =
    new FocusAdapter {
      override def focusGained(e: FocusEvent): Unit = handle_focus()
    }

  private lazy val key_listener =
    new KeyAdapter {
      override def keyPressed(e: KeyEvent): Unit = {
        if (!e.isConsumed() && e.getKeyCode == KeyEvent.VK_ENTER) {
          e.consume()
          handle_tree_selection()
        }
      }
    }

  private lazy val mouse_listener =
    new MouseAdapter {
      override def mousePressed(e: MouseEvent): Unit = {
        if (!e.isConsumed() && e.getClickCount == 1) {
          val path = tree.getPathForLocation(e.getX, e.getY)
          if (path != null) {
            e.consume()
            handle_tree_selection(path = path)
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
      resizeWeight = 0.5
      oneTouchExpandable = true
      leftComponent = tree_pane
      rightComponent = text_pane
    }

  def split_pane_layout(open: Boolean = search_activated): Unit = {
    split_pane.peer.getUI match {
      case ui: BasicSplitPaneUI =>
        val div = ui.getDivider

        val orientation = split_pane.orientation
        val location = split_pane.dividerLocation
        val insets = split_pane.peer.getInsets

        val (left_collapsed, right_collapsed) =
          if (orientation == Orientation.Vertical) {
            (location == insets.left,
              location == (split_pane.peer.getWidth - div.getWidth - insets.right))
          }
          else {
            (location == insets.top,
              location == (split_pane.peer.getHeight - div.getHeight - insets.bottom))
          }

        def click(i: Int): Unit = {
          val comp =
            try { div.getComponent(i) }
            catch { case _: ArrayIndexOutOfBoundsException => null }
          comp match {
            case button: JButton => button.doClick()
            case _ =>
          }
        }

        if (open && left_collapsed) click(1)
        else if (open && right_collapsed || !open && !left_collapsed) click(0)
        else if (!open && right_collapsed) {
          click(0)
          GUI_Thread.later { click(0) }  // FIXME!?
        }
      case _ =>
    }
  }

  def setup(parent: JComponent): Unit = {
    parent.addHierarchyListener(hierarchy_listener)
    parent.addComponentListener(component_listener)
    parent.addFocusListener(focus_listener)
    tree.addKeyListener(key_listener)
    tree.addMouseListener(mouse_listener)
    tree.setCellRenderer(tree_cell_renderer)
  }

  def init(): Unit = {
    handle_update()
    handle_resize()
  }

  def exit(): Unit = {
    delay_resize.revoke()
    delay_shown.revoke()
  }
}
