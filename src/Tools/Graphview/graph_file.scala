/*  Title:      Tools/Graphview/graph_file.scala
    Author:     Makarius

File system operations for graph output.
*/

package isabelle.graphview


import isabelle._

import java.io.{File => JFile}
import java.awt.{Color, Graphics2D}


object Graph_File
{
  def write(file: JFile, graphview: Graphview)
  {
    val box = graphview.bounding_box()
    val w = box.width.ceil.toInt
    val h = box.height.ceil.toInt

    def paint(gfx: Graphics2D)
    {
      gfx.setColor(graphview.background_color)
      gfx.fillRect(0, 0, w, h)
      gfx.translate(- box.x, - box.y)
      graphview.paint(gfx)
    }

    val name = file.getName
    if (name.endsWith(".png")) Graphics_File.write_png(file, paint, w, h)
    else if (name.endsWith(".pdf")) Graphics_File.write_pdf(file, paint, w, h)
    else error("Bad type of file: " + quote(name) + " (.png or .pdf expected)")
  }

  def write(options: Options, file: JFile, graph: Graph_Display.Graph)
  {
    val the_options = options
    val graphview =
      new Graphview(graph.transitive_reduction_acyclic) { def options = the_options }
    graphview.update_layout()

    write(file, graphview)
  }

  def make_pdf(options: Options, graph: Graph_Display.Graph): Bytes =
    Isabelle_System.with_tmp_file("graph", ext = "pdf")(graph_file =>
    {
      write(options, graph_file.file, graph)
      Bytes.read(graph_file)
    })
}
