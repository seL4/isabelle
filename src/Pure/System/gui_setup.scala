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
    Swing_Thread.later {
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
      columns = 80
      rows = 20
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
    text.append("JVM platform: " + Platform.jvm_platform + "\n")
    if (Platform.is_windows)
      text.append("Cygwin root: " + Cygwin.check_root() + "\n")
    try {
      val isabelle_system = new Isabelle_System
      text.append("Isabelle home: " + isabelle_system.getenv("ISABELLE_HOME") + "\n")
      text.append("Isabelle platform: " + isabelle_system.getenv("ISABELLE_PLATFORM") + "\n")
      val platform64 = isabelle_system.getenv("ISABELLE_PLATFORM64")
      if (platform64 != "") text.append("Isabelle platform (64 bit): " + platform64 + "\n")
      text.append("Isabelle java: " + isabelle_system.this_java() + "\n")
    } catch {
      case e: RuntimeException => text.append(e.getMessage + "\n")
    }

    // reactions
    listenTo(ok)
    reactions += {
      case ButtonClicked(`ok`) => System.exit(0)
    }
  }
}

