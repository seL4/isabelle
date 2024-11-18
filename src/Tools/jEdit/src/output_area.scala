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
import org.gjt.sp.jedit.buffer.JEditBuffer


object Output_Area {
  sealed case class Search_Result(
    buffer: JEditBuffer,
    regex: Regex,
    line: Int,
    line_range: Text.Range
  ) {
    lazy val match_ranges: List[Text.Range] = JEdit_Lib.search_text(buffer, line_range, regex)
    lazy val line_text: String = JEdit_Lib.get_text(buffer, line_range).get
    lazy val gui_text: String = "<b>% 3d".format(line) + ":</b> " + Library.trim_line(line_text)
    override def toString: String = gui_text
  }

  sealed case class Search_Results(
    buffer: JEditBuffer,
    pattern: Option[Regex],
    results: List[Search_Result]
  ) {
    def update(start_offset: Int): (Int, Search_Results) =
    pattern match {
      case None => (results.length, this)
      case Some(regex) =>
        val start_line = buffer.getLineOfOffset(start_offset)
        val results1 = results.takeWhile(result => result.line < start_line)
        val results2 =
          List.from(
            for {
              line <- (start_line until buffer.getLineCount).iterator
              line_range = JEdit_Lib.line_range(buffer, line)
              if JEdit_Lib.can_search_text(buffer, line_range, regex)
            } yield Search_Result(buffer, regex, line, line_range))
        (results1.length, copy(results = results1 ::: results2))
    }
  }
}

class Output_Area(view: View, root_name: String = "Overview") {
  GUI_Thread.require {}


  /* tree view */

  val tree: Tree_View =
    new Tree_View(root = Tree_View.Node(root_name), single_selection_mode = true)


  /* text area */

  val pretty_text_area: Pretty_Text_Area = new Pretty_Text_Area(view)

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
