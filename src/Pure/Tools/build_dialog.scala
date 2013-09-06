/*  Title:      Pure/Tools/build_dialog.scala
    Author:     Makarius

Dialog for session build process.
*/

package isabelle


import java.awt.{GraphicsEnvironment, Point, Font}

import scala.swing.{ScrollPane, Button, CheckBox, FlowPanel,
  BorderPanel, MainFrame, TextArea, SwingApplication, Component, Label}
import scala.swing.event.ButtonClicked


object Build_Dialog
{
  /* command line entry point */

  def main(args: Array[String]) =
  {
    GUI.init_laf()
    try {
      args.toList match {
        case
          logic_option ::
          logic ::
          Properties.Value.Boolean(system_mode) ::
          include_dirs =>
            val options = Options.init()
            val dirs = include_dirs.map(Path.explode(_))
            val session =
              Isabelle_System.default_logic(logic,
                if (logic_option != "") options.string(logic_option) else "")

            if (!dialog(options, system_mode, dirs, session, (rc: Int) => sys.exit(rc)))
              sys.exit(0)

        case _ => error("Bad arguments:\n" + cat_lines(args))
      }
    }
    catch {
      case exn: Throwable =>
        GUI.error_dialog(null, "Isabelle build failure", GUI.scrollable_text(Exn.message(exn)))
        sys.exit(2)
    }
  }


  /* dialog */

  def dialog(options: Options, system_mode: Boolean, dirs: List[Path], session: String,
    continue: Int => Unit): Boolean =
  {
    val more_dirs = dirs.map((false, _))

    if (Build.build(options = options, build_heap = true, no_build = true,
        more_dirs = more_dirs, sessions = List(session)) == 0) false
    else {
      Swing_Thread.later {
        val top = build_dialog(options, system_mode, more_dirs, session, continue)
        top.pack()

        val point = GraphicsEnvironment.getLocalGraphicsEnvironment().getCenterPoint()
        top.location =
          new Point(point.x - top.size.width / 2, point.y - top.size.height / 2)

        top.visible = true
      }
      true
    }
  }

  def build_dialog(
    options: Options,
    system_mode: Boolean,
    more_dirs: List[(Boolean, Path)],
    session: String,
    continue: Int => Unit): MainFrame = new MainFrame
  {
    iconImage = GUI.isabelle_image()


    /* GUI state */

    @volatile private var is_stopped = false
    private var return_code = 2

    def close(rc: Int) { visible = false; continue(rc) }
    override def closeOperation { close(return_code) }


    /* text */

    val text = new TextArea {
      font = new Font("SansSerif", Font.PLAIN, GUI.resolution_scale(10) max 14)
      editable = false
      columns = 50
      rows = 20
    }

    val scroll_text = new ScrollPane(text)

    val progress = new Build.Progress
    {
      override def echo(msg: String): Unit =
        Swing_Thread.later {
          text.append(msg + "\n")
          val vertical = scroll_text.peer.getVerticalScrollBar
          vertical.setValue(vertical.getMaximum)
        }
      override def theory(session: String, theory: String): Unit =
        echo(session + ": theory " + theory)
      override def stopped: Boolean = is_stopped
    }


    /* layout panel with dynamic actions */

    val action_panel = new FlowPanel(FlowPanel.Alignment.Center)()
    val layout_panel = new BorderPanel
    layout_panel.layout(scroll_text) = BorderPanel.Position.Center
    layout_panel.layout(action_panel) = BorderPanel.Position.South

    contents = layout_panel

    def set_actions(cs: Component*)
    {
      action_panel.contents.clear
      action_panel.contents ++= cs
      layout_panel.revalidate
      layout_panel.repaint
    }


    /* actions */

    var do_auto_close = true
    def check_auto_close(): Unit =
      if (do_auto_close && return_code == 0) close(return_code)

    val auto_close = new CheckBox("Auto close") {
      reactions += {
        case ButtonClicked(_) => do_auto_close = this.selected
        check_auto_close()
      }
    }
    auto_close.selected = do_auto_close
    auto_close.tooltip = "Automatically close dialog when finished"


    val stop_button = new Button("Stop") {
      reactions += {
        case ButtonClicked(_) =>
          is_stopped = true
          set_actions(new Label("Stopping ..."))
      }
    }

    set_actions(stop_button, auto_close)


    /* exit */

    val delay_exit =
      Swing_Thread.delay_first(Time.seconds(1.0))
      {
        check_auto_close()
        val button =
          new Button(if (return_code == 0) "OK" else "Exit") {
            reactions += { case ButtonClicked(_) => close(return_code) }
          }
        set_actions(button)
        button.peer.getRootPane.setDefaultButton(button.peer)
      }


    /* main build */

    title = "Isabelle build (" + Isabelle_System.getenv("ML_IDENTIFIER") + ")"
    progress.echo("Build started for Isabelle/" + session + " ...")

    default_thread_pool.submit(() => {
      val (out, rc) =
        try {
          ("",
            Build.build(options = options, progress = progress,
              build_heap = true, more_dirs = more_dirs,
              system_mode = system_mode, sessions = List(session)))
        }
        catch { case exn: Throwable => (Exn.message(exn) + "\n", 2) }
      Swing_Thread.now {
        progress.echo(out + (if (rc == 0) "OK\n" else "Return code: " + rc + "\n"))
        return_code = rc
        delay_exit.invoke()
      }
    })
  }
}

