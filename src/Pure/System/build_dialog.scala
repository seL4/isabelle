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


    /* controls */

    private var clean_build = false
    private var system_build = false
    private var verbose = false

    private val clean = new CheckBox("Clean build") {
      reactions += { case ButtonClicked(_) => clean_build = this.selected }
    }
    clean.selected = clean_build
    clean.tooltip = "Delete outdated session images"

    private val system = new CheckBox("System build") {
      reactions += { case ButtonClicked(_) => system_build = this.selected }
    }
    system.selected = system_build
    system.tooltip = "Produce output in $ISABELLE_HOME instead of $ISABELLE_HOME_USER"

    private val verbose_mode = new CheckBox("Verbose mode") {
      reactions += { case ButtonClicked(_) => verbose = this.selected }
    }
    verbose_mode.selected = verbose
    verbose_mode.tooltip = "More output during build process"

    val controls = new FlowPanel(FlowPanel.Alignment.Right)(clean, system, verbose_mode)


    /* text */

    val text = new TextArea {
      editable = false
      columns = 80
      rows = 15
    }


    /* actions */

    val ok = new Button { text = "OK" }
    val ok_panel = new FlowPanel(FlowPanel.Alignment.Center)(ok)

    listenTo(ok)
    reactions += {
      case ButtonClicked(`ok`) => sys.exit(0)
    }


    /* main panel */

    val panel = new BorderPanel
    panel.layout(controls) = BorderPanel.Position.North
    panel.layout(new ScrollPane(text)) = BorderPanel.Position.Center
    panel.layout(ok_panel) = BorderPanel.Position.South
    contents = panel
  }
}

