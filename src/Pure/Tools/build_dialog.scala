/*  Title:      Pure/Tools/build_dialog.scala
    Author:     Makarius

Dialog for session build process.
*/

package isabelle


import java.awt.{GraphicsEnvironment, Point, Font}

import scala.swing.{ScrollPane, Button, CheckBox, FlowPanel,
  BorderPanel, MainFrame, TextArea, SwingApplication}
import scala.swing.event.ButtonClicked


object Build_Dialog
{
  def main(args: Array[String]) =
  {
    Platform.init_laf()
    try {
      args.toList match {
        case
          logic_option ::
          logic ::
          Properties.Value.Boolean(system_mode) ::
          include_dirs =>
            val more_dirs = include_dirs.map(s => ((false, Path.explode(s))))

            val options = Options.init()
            val session =
              Isabelle_System.default_logic(logic,
                if (logic_option != "") options.string(logic_option) else "")

            if (Build.build(Build.Ignore_Progress, options, build_heap = true, no_build = true,
                more_dirs = more_dirs, sessions = List(session)) == 0) sys.exit(0)
            else
              Swing_Thread.later {
                val top = build_dialog(options, system_mode, more_dirs, session)
                top.pack()

                val point = GraphicsEnvironment.getLocalGraphicsEnvironment().getCenterPoint()
                top.location =
                  new Point(point.x - top.size.width / 2, point.y - top.size.height / 2)

                top.visible = true
              }
        case _ => error("Bad arguments:\n" + cat_lines(args))
      }
    }
    catch {
      case exn: Throwable =>
        Library.error_dialog(null, "Isabelle build failure",
          Library.scrollable_text(Exn.message(exn)))
        sys.exit(2)
    }
  }


  def build_dialog(
    options: Options,
    system_mode: Boolean,
    more_dirs: List[(Boolean, Path)],
    session: String): MainFrame = new MainFrame
  {
    /* GUI state */

    private var is_stopped = false
    private var return_code = 2

    override def closeOperation { sys.exit(return_code) }


    /* text */

    val text = new TextArea {
      font = new Font("SansSerif", Font.PLAIN, 14)
      editable = false
      columns = 40
      rows = 10
    }

    val progress = new Build.Progress
    {
      override def theory(name: String): Unit = echo("  theory " + name)
      override def echo(msg: String): Unit = Swing_Thread.now { text.append(msg + "\n") }
      override def stopped: Boolean =
        Swing_Thread.now { val b = is_stopped; is_stopped = false; b  }
    }


    /* action button */

    var button_action: () => Unit = (() => is_stopped = true)
    val button = new Button("Cancel") {
      reactions += { case ButtonClicked(_) => button_action() }
    }
    def button_exit(rc: Int)
    {
      button.text = if (rc == 0) "OK" else "Exit"
      button_action = (() => sys.exit(rc))
      button.peer.getRootPane.setDefaultButton(button.peer)
    }

    val action_panel = new FlowPanel(FlowPanel.Alignment.Center)(button)


    /* layout panel */

    val layout_panel = new BorderPanel
    layout_panel.layout(new ScrollPane(text)) = BorderPanel.Position.Center
    layout_panel.layout(action_panel) = BorderPanel.Position.South

    contents = layout_panel


    /* main build */

    title = "Isabelle build (" + Isabelle_System.getenv("ML_IDENTIFIER") + ")"
    progress.echo("Build started for Isabelle/" + session + " ...")

    default_thread_pool.submit(() => {
      val (out, rc) =
        try {
          ("",
            Build.build(progress, options, build_heap = true, more_dirs = more_dirs,
              system_mode = system_mode, sessions = List(session)))
        }
        catch { case exn: Throwable => (Exn.message(exn) + "\n", 2) }
      Swing_Thread.now {
        progress.echo(out + (if (rc == 0) "OK\n" else "Return code: " + rc + "\n"))
        return_code = rc
        button_exit(rc)
      }
    })
  }
}

