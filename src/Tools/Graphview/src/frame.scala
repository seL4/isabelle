/*  Title:      Tools/Graphview/src/frame.scala
    Author:     Markus Kaiser, TU Muenchen

Graphview standalone frame.
*/

package isabelle.graphview


import isabelle._

import java.awt.Dimension
import scala.swing.{MainFrame, BorderPanel, Window, SwingApplication}
import javax.swing.border.EmptyBorder


object Frame extends SwingApplication
{
  def startup(args : Array[String])
  {
    // FIXME avoid I/O etc. on Swing thread
    val graph: Model.Graph =
      try {
        Platform.init_laf()
        Isabelle_System.init()

        args.toList match {
          case List(arg) =>
            Model.decode_graph(YXML.parse_body(File.read(Path.explode(arg))))
          case _ => error("Bad arguments:\n" + cat_lines(args))
        }
      }
      catch { case exn: Throwable => println(Exn.message(exn)); sys.exit(1) }

    val top = new MainFrame {
      title = "Graphview"
      minimumSize = new Dimension(640, 480)
      preferredSize = new Dimension(800, 600)

      contents = new BorderPanel {
        border = new EmptyBorder(5, 5, 5, 5)

        add(new Main_Panel(graph), BorderPanel.Position.Center)
      }
    }

    top.pack()
    top.visible = true
  }
}