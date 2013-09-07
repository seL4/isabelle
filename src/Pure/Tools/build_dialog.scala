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

  def main(args: Array[String])
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

            val system_dialog = new System_Dialog
            dialog(options, system_dialog, system_mode, dirs, session)
            sys.exit(system_dialog.join)

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

  def dialog(
    options: Options,
    system_dialog: System_Dialog,
    system_mode: Boolean,
    dirs: List[Path],
    session: String)
  {
    val more_dirs = dirs.map((false, _))

    if (Build.build(options = options, build_heap = true, no_build = true,
        more_dirs = more_dirs, sessions = List(session)) == 0)
      system_dialog.return_code(0)
    else {
      system_dialog.title("Isabelle build (" + Isabelle_System.getenv("ML_IDENTIFIER") + ")")
      system_dialog.echo("Build started for Isabelle/" + session + " ...")

      val (out, rc) =
        try {
          ("",
            Build.build(options = options, progress = system_dialog,
              build_heap = true, more_dirs = more_dirs,
              system_mode = system_mode, sessions = List(session)))
        }
        catch { case exn: Throwable => (Exn.message(exn) + "\n", 2) }

      system_dialog.echo(out + (if (rc == 0) "OK\n" else "Return code: " + rc + "\n"))
      system_dialog.return_code(rc)
    }
  }
}

