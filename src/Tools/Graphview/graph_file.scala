/*  Title:      Tools/Graphview/graph_file.scala
    Author:     Makarius

File system operations for graph output.
*/

package isabelle.graphview


import isabelle._

import java.io.{File => JFile}
import java.awt.Graphics2D


object Graph_File {
  def write(file: JFile, graphview: Graphview): Unit = {
    val box = graphview.bounding_box()
    val w = box.width.ceil.toInt
    val h = box.height.ceil.toInt

    def paint(gfx: Graphics2D): Unit = {
      gfx.setColor(graphview.background_color)
      gfx.fillRect(0, 0, w, h)
      gfx.translate(- box.x, - box.y)
      graphview.paint(gfx)
    }

    val name = file.getName
    if (File.is_png(name)) Graphics_File.write_png(file, paint, w, h)
    else if (File.is_pdf(name)) Graphics_File.write_pdf(file, paint, w, h)
    else error("Bad type of file: " + quote(name) + " (.png or .pdf expected)")
  }

  def write(options: Options, file: JFile, graph: Graph_Display.Graph): Unit = {
    val graphview_options = options
    val graphview =
      new Graphview(graph.transitive_reduction_acyclic) {
        def options: Options = graphview_options
      }
    graphview.update_layout()
    write(file, graphview)
  }

  def make_pdf(options: Options, graph: Graph_Display.Graph): Bytes =
    Isabelle_System.with_tmp_file("graph", ext = "pdf") { graph_file =>
      write(options, graph_file.file, graph)
      Bytes.read(graph_file)
    }
}
