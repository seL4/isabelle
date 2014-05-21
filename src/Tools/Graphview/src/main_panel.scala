/*  Title:      Tools/Graphview/src/main_panel.scala
    Author:     Markus Kaiser, TU Muenchen

Graph Panel wrapper.
*/

package isabelle.graphview


import isabelle._
import isabelle.graphview.Mutators._

import scala.collection.JavaConversions._
import scala.swing.{BorderPanel, Button, BoxPanel,
  Orientation, Swing, CheckBox, Action, FileChooser}

import java.io.File
import java.awt.{Color, Dimension}
import java.awt.geom.Rectangle2D
import java.awt.image.BufferedImage
import javax.imageio.ImageIO
import javax.swing.border.EmptyBorder
import javax.swing.JComponent


class Main_Panel(graph: Model.Graph)
  extends BorderPanel
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
  chooser.title = "Graph export"

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
      action = Action("Save as PNG"){
        chooser.showSaveDialog(this) match {
          case FileChooser.Result.Approve => export(chooser.selectedFile)
          case _ =>
        }
      }
    }
    contents += Swing.RigidBox(new Dimension(10, 0))
    contents += graph_panel.zoom_box

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

  private def export(file: File) {
    val (minX, minY, maxX, maxY) = visualizer.Coordinates.bounds
    val img = new BufferedImage((math.abs(maxX - minX) + 400).toInt,
                                (math.abs(maxY - minY) + 200).toInt,
                                BufferedImage.TYPE_INT_RGB)
    val g = img.createGraphics
    g.setColor(Color.WHITE)
    g.fill(new Rectangle2D.Double(0, 0, img.getWidth(), img.getHeight()))

    g.translate(- minX + 200, - minY + 100)
    visualizer.Drawer.paint_all_visible(g, false)
    g.dispose()

    try { ImageIO.write(img, "png", file) }
    catch { case ex: Exception => ex.printStackTrace }  // FIXME !?
  }
}
