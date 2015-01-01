/*  Title:      Tools/Graphview/main_panel.scala
    Author:     Markus Kaiser, TU Muenchen

Graph Panel wrapper.
*/

package isabelle.graphview


import isabelle._

import scala.collection.JavaConversions._
import scala.swing.{BorderPanel, Button, BoxPanel,
  Orientation, Swing, CheckBox, Action, FileChooser}

import java.io.{File => JFile}
import java.awt.{Color, Dimension, Graphics2D}
import java.awt.geom.Rectangle2D
import java.awt.image.BufferedImage
import javax.imageio.ImageIO
import javax.swing.border.EmptyBorder
import javax.swing.JComponent


class Main_Panel(graph: Model.Graph) extends BorderPanel
{
  focusable = true
  requestFocus()

  val model = new Model(graph)
  val visualizer = new Visualizer(model)

  def make_tooltip(parent: JComponent, x: Int, y: Int, body: XML.Body): String = null
  val graph_panel = new Graph_Panel(visualizer, make_tooltip)

  listenTo(keys)
  reactions += graph_panel.reactions

  val mutator_dialog = new Mutator_Dialog(visualizer, model.Mutators, "Filters", "Hide", false)

  val color_dialog = new Mutator_Dialog(visualizer, model.Colors, "Colorations")

  private val chooser = new FileChooser()
  chooser.fileSelectionMode = FileChooser.SelectionMode.FilesOnly
  chooser.title = "Save Image (.png or .pdf)"

  val options_panel = new BoxPanel(Orientation.Horizontal) {
    border = new EmptyBorder(0, 0, 10, 0)

    contents += Swing.HGlue
    contents += new CheckBox(){
      selected = visualizer.arrow_heads
      action = Action("Arrow Heads"){
        visualizer.arrow_heads = selected
        graph_panel.repaint()
      }
    }
    contents += Swing.RigidBox(new Dimension(10, 0))
    contents += new Button{
      action = Action("Save Image"){
        chooser.showSaveDialog(this) match {
          case FileChooser.Result.Approve => export(chooser.selectedFile)
          case _ =>
        }
      }
    }
    contents += Swing.RigidBox(new Dimension(10, 0))
    contents += graph_panel.zoom

    contents += Swing.RigidBox(new Dimension(10, 0))
    contents += new Button{
      action = Action("Apply Layout"){
        graph_panel.apply_layout()
      }
    }
    contents += Swing.RigidBox(new Dimension(10, 0))
    contents += new Button{
      action = Action("Fit to Window"){
        graph_panel.fit_to_window()
      }
    }
    contents += Swing.RigidBox(new Dimension(10, 0))
    contents += new Button{
      action = Action("Colorations"){
        color_dialog.open
      }
    }
    contents += Swing.RigidBox(new Dimension(10, 0))
    contents += new Button{
      action = Action("Filters"){
        mutator_dialog.open
      }
    }
  }

  add(graph_panel, BorderPanel.Position.Center)
  add(options_panel, BorderPanel.Position.North)

  private def export(file: JFile)
  {
    val (x0, y0, x1, y1) = visualizer.Coordinates.bounds
    val w = (math.abs(x1 - x0) + 400).toInt
    val h = (math.abs(y1 - y0) + 200).toInt

    def paint(gfx: Graphics2D)
    {
      gfx.setColor(Color.WHITE)
      gfx.fill(new Rectangle2D.Double(0, 0, w, h))

      gfx.translate(- x0 + 200, - y0 + 100)
      visualizer.Drawer.paint_all_visible(gfx, false)
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
