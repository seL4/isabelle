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
  def write(file: JFile, visualizer: Visualizer)
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

    val name = file.getName
    if (name.endsWith(".png")) Graphics_File.write_png(file, paint _, w, h)
    else if (name.endsWith(".pdf")) Graphics_File.write_pdf(file, paint _, w, h)
    else error("Bad type of file: " + quote(name) + " (.png or .pdf expected)")
  }

  def write(options: Options, file: JFile, graph: Graph_Display.Graph)
  {
    val model = new Model(graph.transitive_reduction_acyclic)

    val the_options = options
    val visualizer = new Visualizer(model) { def options = the_options }
    visualizer.update_layout()

    write(file, visualizer)
  }
}
