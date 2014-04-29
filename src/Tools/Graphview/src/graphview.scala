/*  Title:      Tools/Graphview/src/graphview.scala
    Author:     Markus Kaiser, TU Muenchen

Graphview standalone application.
*/

package isabelle.graphview


import isabelle._

import java.awt.Dimension
import scala.swing.{MainFrame, BorderPanel, Window, SwingApplication}
import javax.swing.border.EmptyBorder
import javax.swing.ToolTipManager


object Graphview extends SwingApplication
{
  def startup(args : Array[String])
  {
    // FIXME avoid I/O etc. on Swing thread
    val graph: Model.Graph =
      try {
        GUI.init_laf()
        Isabelle_System.init()
        Isabelle_Font.install_fonts()
        ToolTipManager.sharedInstance.setDismissDelay(1000*60*60)

        args.toList match {
          case List(arg) =>
            Model.decode_graph(YXML.parse_body(Symbol.decode(File.read(Path.explode(arg)))))
              .transitive_reduction_acyclic
          case _ => error("Bad arguments:\n" + cat_lines(args))
        }
      }
      catch { case exn: Throwable => Output.error_message(Exn.message(exn)); sys.exit(1) }

    val top = new MainFrame {
      iconImage = GUI.isabelle_image()

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