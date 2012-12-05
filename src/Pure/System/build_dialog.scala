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
        case Command_Line.Chunks(include_dirs, List(session)) =>
          val top = build_dialog(include_dirs.map(Path.explode), session)
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


  def build_dialog(include_dirs: List[Path], session: String): MainFrame = new MainFrame
  {
    title = "Isabelle session build"


    /* GUI state */

    private var clean_build = false
    private var system_mode = false

    private var is_started = false
    private var is_stopped = false
    private var return_code = 0


    /* controls */

    private val _clean_build = new CheckBox("Clean build") {
      reactions += { case ButtonClicked(_) => clean_build = this.selected }
    }
    _clean_build.selected = clean_build
    _clean_build.tooltip = "Delete outdated session images"

    private val _system_mode = new CheckBox("System build") {
      reactions += { case ButtonClicked(_) => system_mode = this.selected }
    }
    _system_mode.selected = system_mode
    _system_mode.tooltip = "Produce output in $ISABELLE_HOME instead of $ISABELLE_HOME_USER"

    val controls = new FlowPanel(FlowPanel.Alignment.Right)(_clean_build, _system_mode)


    /* text */

    val text = new TextArea {
      editable = false
      columns = 80
      rows = 15
    }

    val progress = new Build.Progress
    {
      override def echo(msg: String): Unit = Swing_Thread.now { text.append(msg + "\n") }
      override def stopped: Boolean =
        Swing_Thread.now { val b = is_stopped; is_stopped = false; b  }
    }


    /* actions */

    val start = new Button("Start") {
      reactions += { case ButtonClicked(_) =>
        if (!is_started) {
          progress.echo("Build started ...")
          is_started = true
          default_thread_pool.submit(() => {
            val (out, rc) =
              try {
                ("",
                  Build.build(progress, build_heap = true, verbose = true,
                    clean_build = clean_build, system_mode = system_mode, sessions = List(session)))
              }
              catch { case exn: Throwable => (Exn.message(exn) + "\n", 2) }
            Swing_Thread.now {
              if (rc != 0) {
                progress.echo(out + "Return code: " + rc + "\n")
                return_code = rc
              }
              is_started = false
            }
          })
        }
      }
    }

    val stop = new Button("Stop") {
      reactions += { case ButtonClicked(_) =>
        progress.echo("Build stopped ...")
        is_stopped = true
      }
    }

    val exit = new Button("Exit") {
      reactions += { case ButtonClicked(_) => sys.exit(return_code) }
    }

    val actions = new FlowPanel(FlowPanel.Alignment.Center)(start, stop, exit)


    /* layout panel */

    val layout_panel = new BorderPanel
    layout_panel.layout(controls) = BorderPanel.Position.North
    layout_panel.layout(new ScrollPane(text)) = BorderPanel.Position.Center
    layout_panel.layout(actions) = BorderPanel.Position.South

    contents = layout_panel
  }
}

