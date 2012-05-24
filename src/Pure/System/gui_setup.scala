/*  Title:      Pure/System/gui_setup.scala
    Author:     Makarius

GUI for basic system setup.
*/

package isabelle

import java.lang.System

import scala.swing.{ScrollPane, Button, FlowPanel,
  BorderPanel, MainFrame, TextArea, SwingApplication}
import scala.swing.event.ButtonClicked


object GUI_Setup extends SwingApplication
{
  def startup(args: Array[String]) =
  {
    Platform.init_laf()
    top.pack()
    top.visible = true
  }

  def top = new MainFrame {
    title = "Isabelle setup"

    // components
    val text = new TextArea {
      editable = false
      columns = 80
      rows = 20
    }
    val ok = new Button { text = "OK" }
    val ok_panel = new FlowPanel(FlowPanel.Alignment.Center)(ok)

    val panel = new BorderPanel
    panel.layout(new ScrollPane(text)) = BorderPanel.Position.Center
    panel.layout(ok_panel) = BorderPanel.Position.South
    contents = panel

    // values
    if (Platform.is_windows)
      text.append("Cygwin root: " + Standard_System.cygwin_root() + "\n")
    text.append("JVM name: " + Platform.jvm_name + "\n")
    text.append("JVM platform: " + Platform.jvm_platform + "\n")
    text.append("JVM home: " + java.lang.System.getProperty("java.home") + "\n")
    try {
      Isabelle_System.init()
      text.append("ML platform: " + Isabelle_System.getenv("ML_PLATFORM") + "\n")
      text.append("Isabelle platform: " + Isabelle_System.getenv("ISABELLE_PLATFORM") + "\n")
      val platform64 = Isabelle_System.getenv("ISABELLE_PLATFORM64")
      if (platform64 != "") text.append("Isabelle platform (64 bit): " + platform64 + "\n")
      text.append("Isabelle home: " + Isabelle_System.getenv("ISABELLE_HOME") + "\n")
      val isabelle_home_windows = Isabelle_System.getenv("ISABELLE_HOME_WINDOWS")
      if (isabelle_home_windows != "")
        text.append("Isabelle home (Windows): " + isabelle_home_windows + "\n")
      text.append("Isabelle jdk home: " + Isabelle_System.getenv("ISABELLE_JDK_HOME") + "\n")
    }
    catch { case ERROR(msg) => text.append(msg + "\n") }

    // reactions
    listenTo(ok)
    reactions += {
      case ButtonClicked(`ok`) => System.exit(0)
    }
  }
}

