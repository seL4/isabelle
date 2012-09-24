/*  Title:      Tools/Graphview/src/frame.scala
    Author:     Markus Kaiser, TU Muenchen

Graphview standalone frame.
*/

package isabelle.graphview


import isabelle._

import java.awt.Dimension
import scala.swing.{MainFrame, BorderPanel, Window, SwingApplication}
import javax.swing.border.EmptyBorder


object Graphview_Frame extends SwingApplication
{
  def startup(args : Array[String])
  {
    try {
      Platform.init_laf()
      Isabelle_System.init()
    }
    catch { case exn: Throwable => println(Exn.message(exn)); System.exit(1) }

    val opt_xml: Option[XML.Tree] =
      try {
        Some(YXML.parse_body(
            Symbol.decode(io.Source.fromFile(args(0)).mkString)).head)
      } catch {
        case _ : ArrayIndexOutOfBoundsException => None
        case _ : java.io.FileNotFoundException => None
      }
    
    //Textfiles will still be valid and result in an empty frame
    //since they are valid to YXML.
    opt_xml match {
      case None =>
        println("No valid YXML-File given.\n" +
          "Usage: java -jar graphview.jar <yxmlfile>")
        System.exit(1)
      case Some(xml) =>
        val top = frame(xml)
        top.pack()
        top.visible = true
    }

    def frame(xml: XML.Tree): Window = new MainFrame {
      title = "Graphview"
      minimumSize = new Dimension(640, 480)
      preferredSize = new Dimension(800, 600)

      contents = new BorderPanel {
        border = new EmptyBorder(5, 5, 5, 5)

        add(new Main_Panel(xml), BorderPanel.Position.Center)
      }
    }
  }
}