/*  Title:      Pure/System/build_dialog.scala
    Author:     Makarius

Dialog for session build process.
*/

package isabelle


import scala.swing.{ScrollPane, Button, CheckBox, FlowPanel,
  BorderPanel, MainFrame, TextArea, SwingApplication}
import scala.swing.event.ButtonClicked


object Build_Dialog extends SwingApplication
{
  def startup(args: Array[String]) =
  {
    Platform.init_laf()

    try {
      args.toList match {
        case
          Properties.Value.Boolean(system_mode) ::
          session :: include_dirs =>
            val top = build_dialog(system_mode, include_dirs.map(Path.explode), session)
            top.pack()
            top.visible = true
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
    system_mode: Boolean,
    include_dirs: List[Path],
    session: String): MainFrame = new MainFrame
  {
    title = "Isabelle build"


    /* GUI state */

    private var is_stopped = false
    private var return_code = 0


    /* text */

    val text = new TextArea {
      editable = false
      columns = 40
      rows = 10
    }

    val progress = new Build.Progress
    {
      override def echo(msg: String): Unit = Swing_Thread.now { text.append(msg + "\n") }
      override def stopped: Boolean =
        Swing_Thread.now { val b = is_stopped; is_stopped = false; b  }
    }


    /* actions */

    val cancel = new Button("Cancel") {
      reactions += { case ButtonClicked(_) => is_stopped = true }
    }

    val actions = new FlowPanel(FlowPanel.Alignment.Center)(cancel)


    /* layout panel */

    val layout_panel = new BorderPanel
    layout_panel.layout(new ScrollPane(text)) = BorderPanel.Position.Center
    layout_panel.layout(actions) = BorderPanel.Position.South

    contents = layout_panel


    /* main build */

    progress.echo("Build started ...")

    default_thread_pool.submit(() => {
      val (out, rc) =
        try {
          ("",
            Build.build(progress, build_heap = true,
              system_mode = system_mode, sessions = List(session)))
        }
        catch { case exn: Throwable => (Exn.message(exn) + "\n", 2) }
      if (rc == 0) {
        progress.echo("OK\n")
        Thread.sleep(1000)
      }
      else
        Swing_Thread.now {
          Library.error_dialog(this.peer, "Isabelle build failure",
            Library.scrollable_text(out + "Return code: " + rc + "\n"))
        }
      sys.exit(rc)
    })
  }
}

