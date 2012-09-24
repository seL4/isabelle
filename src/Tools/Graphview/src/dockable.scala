/*  Title:      Tools/Graphview/src/dockable.scala
    Author:     Markus Kaiser, TU Muenchen

Graphview jEdit dockable.
*/

package isabelle.graphview


import isabelle._
import isabelle.jedit._

import scala.actors.Actor._
import scala.swing.{FileChooser}

import java.io.File
import org.gjt.sp.jedit.View


class Graphview_Dockable(view: View, position: String)
extends Dockable(view, position)
{
  //FIXME: How does the xml get here?
  val xml: XML.Tree =
  try {
    val chooser = new FileChooser()
    val path: File = chooser.showOpenDialog(null) match {
        case FileChooser.Result.Approve =>
          chooser.selectedFile
        case _ => new File("~/local_deps.graph")
    }
    YXML.parse_body(Symbol.decode(io.Source.fromFile(path).mkString)).head
  } catch {
    case ex: Exception => System.err.println(ex.getMessage); null
  }


  set_content(new Main_Panel(xml))

  /* main actor */

  private val main_actor = actor {
    loop {
      react {
        case result: Isabelle_Process.Output =>
        case bad => System.err.println("Protocol_Dockable: ignoring bad message " + bad)
      }
    }
  }

  override def init() { }
  override def exit() { }
}
