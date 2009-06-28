/*  Title:      Pure/System/gui_setup.scala
    Author:     Makarius

GUI for basic system setup.
*/

package isabelle

import javax.swing.UIManager

import scala.swing._
import scala.swing.event._


object GUI_Setup extends GUIApplication
{
  def main(args: Array[String]) =
  {
    Swing.later {
      UIManager.setLookAndFeel(Platform.look_and_feel)
      top.pack()
      top.visible = true
    }
  }

  def top = new MainFrame {
    title = "Isabelle setup"
    val ok = new Button { text = "OK" }

    contents = new BoxPanel(Orientation.Vertical) {
      contents += ok
      border = scala.swing.Swing.EmptyBorder(20, 20, 20, 20)
    }

    listenTo(ok)
    reactions += {
      case ButtonClicked(`ok`) => System.exit(0)
    }
  }
}

