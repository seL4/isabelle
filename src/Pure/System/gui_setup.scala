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

    // components
    val text = new TextArea {
      editable = false
      columns = 40
      rows = 15
      xLayoutAlignment = 0.5
    }
    val ok = new Button {
      text = "OK"
      xLayoutAlignment = 0.5
    }
    contents = new BoxPanel(Orientation.Vertical) {
      contents += text
      contents += ok
    }

    // values
    if (Platform.is_windows) {
      text.append("Cygwin root: " + Cygwin.config()._1 + "\n")
    }
    Platform.defaults match {
      case None =>
      case Some((name, None)) => text.append("Platform: " + name + "\n")
      case Some((name1, Some(name2))) =>
        text.append("Main platform: " + name1 + "\n")
        text.append("Alternative platform: " + name2 + "\n")
    }

    // reactions
    listenTo(ok)
    reactions += {
      case ButtonClicked(`ok`) => System.exit(0)
    }
  }
}

