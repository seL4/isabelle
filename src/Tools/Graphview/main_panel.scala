/*  Title:      Tools/Graphview/main_panel.scala
    Author:     Markus Kaiser, TU Muenchen
    Author:     Makarius

Graph Panel wrapper.
*/

package isabelle.graphview


import isabelle._

import scala.swing.{BorderPanel, Button, CheckBox, Action, FileChooser, SplitPane, Orientation}

import java.io.{File => JFile}
import java.awt.{Color, Graphics2D}
import javax.imageio.ImageIO
import javax.swing.border.EmptyBorder
import javax.swing.JComponent


class Main_Panel(model: Model, visualizer: Visualizer) extends BorderPanel
{
  val graph_panel = new Graph_Panel(visualizer)
  val tree_panel = new Tree_Panel(visualizer, graph_panel)

  def update_layout()
  {
    visualizer.update_layout()
    tree_panel.refresh()
    graph_panel.refresh()
  }

  val split_pane =
    if (visualizer.options.bool("graphview_swap_panels"))
      new SplitPane(Orientation.Vertical, tree_panel, graph_panel)
    else
      new SplitPane(Orientation.Vertical, graph_panel, tree_panel)
  split_pane.oneTouchExpandable = true

  val mutator_dialog = new Mutator_Dialog(visualizer, model.Mutators, "Filters", "Hide", false)

  val color_dialog = new Mutator_Dialog(visualizer, model.Colors, "Colorations")

  private val chooser = new FileChooser()
  chooser.fileSelectionMode = FileChooser.SelectionMode.FilesOnly
  chooser.title = "Save image (.png or .pdf)"

  val controls =
    new Wrap_Panel(Wrap_Panel.Alignment.Right)(
      new CheckBox() {
        tooltip = "Show full node content"
        selected = visualizer.show_content
        action = Action("Show content") {
          visualizer.show_content = selected
          update_layout()
        }
      },
      new CheckBox() {
        tooltip = "Draw edges with explicit arrow heads"
        selected = visualizer.show_arrow_heads
        action = Action("Show arrow heads") {
          visualizer.show_arrow_heads = selected
          graph_panel.repaint()
        }
      },
      new CheckBox() {
        tooltip = "Show dummy nodes -- easier mouse dragging"
        selected = visualizer.show_dummies
        action = Action("Show dummies") {
          visualizer.show_dummies = selected
          graph_panel.repaint()
        }
      },
      new Button {
        action = Action("Save image") {
          tooltip = "Save current image as PNG or PDF"
          chooser.showSaveDialog(this) match {
            case FileChooser.Result.Approve => export(chooser.selectedFile)
            case _ =>
          }
        }
      },
      graph_panel.zoom,
      new Button { action = Action("Fit to window") { graph_panel.fit_to_window() } },
      new Button { action = Action("Update layout") { update_layout() } },
      new Button { action = Action("Colorations") { color_dialog.open } },
      new Button { action = Action("Filters") { mutator_dialog.open } })

  layout(split_pane) = BorderPanel.Position.Center
  layout(controls) = BorderPanel.Position.North
  update_layout()

  private def export(file: JFile)
  {
    val box = visualizer.bounding_box()
    val w = box.width.ceil.toInt
    val h = box.height.ceil.toInt

    def paint(gfx: Graphics2D)
    {
      gfx.setColor(Color.WHITE)
      gfx.fillRect(0, 0, w, h)
      gfx.translate(- box.x, - box.y)
      visualizer.paint_all_visible(gfx)
    }

    try {
      val name = file.getName
      if (name.endsWith(".png")) Graphics_File.write_png(file, paint _, w, h)
      else if (name.endsWith(".pdf")) Graphics_File.write_pdf(file, paint _, w, h)
      else error("Bad type of file: " + quote(name) + " (.png or .pdf expected)")
    }
    catch {
      case ERROR(msg) => GUI.error_dialog(this.peer, "Error", GUI.scrollable_text(msg))
    }
  }
}
