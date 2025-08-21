/*  Title:      Tools/jEdit/src/session_build.scala
    Author:     Makarius

Session build management.
*/

package isabelle.jedit


import isabelle._

import java.awt.event.{WindowEvent, WindowAdapter}
import javax.swing.{WindowConstants, JDialog}

import scala.swing.{ScrollPane, FlowPanel, BorderPanel, TextArea, Component, Label}

import org.gjt.sp.jedit.View


object Session_Build {
  def check_dialog(view: View): Unit = {
    Isabelle_Thread.fork() {
      try {
        if (JEdit_Session.session_build_ok()) JEdit_Session.session_start()
        else GUI_Thread.later { new Dialog(view) }
      }
      catch {
        case exn: Throwable =>
          GUI.dialog(view, "Isabelle build", GUI.scrollable_text(Exn.print(exn)))
      }
    }
  }

  private class Dialog(view: View) extends JDialog(view) {
    /* text */

    private val text = new TextArea
    text.editable = false
    text.columns = 60
    text.rows = 24
    text.font = GUI.copy_font(GUI.label_font())
    text.caret.color = text.background

    private val scroll_text = new ScrollPane(text)


    /* progress */

    private val progress = new Progress {
      override def output(message: Progress.Message): Unit =
        if (do_output(message)) {
          GUI_Thread.later {
            text.append(message.output_text + "\n")
            val vertical = scroll_text.peer.getVerticalScrollBar
            vertical.setValue(vertical.getMaximum)
          }
        }

      override def theory(theory: Progress.Theory): Unit =
        output(theory.message.copy(verbose = false))
    }


    /* layout panel with dynamic actions */

    private val action_panel = new FlowPanel(FlowPanel.Alignment.Center)()
    private val layout_panel = new BorderPanel
    layout_panel.layout(scroll_text) = BorderPanel.Position.Center
    layout_panel.layout(action_panel) = BorderPanel.Position.South

    setContentPane(layout_panel.peer)

    private def set_actions(cs: Component*): Unit = {
      action_panel.contents.clear()
      action_panel.contents ++= cs
      layout_panel.revalidate()
      layout_panel.repaint()
    }


    /* return code and exit */

    private var _return_code: Option[Int] = None

    private def return_code(rc: Int): Unit =
      GUI_Thread.later {
        _return_code = Some(rc)
        delay_exit.invoke()
      }

    private val delay_exit =
      Delay.first(Time.seconds(1.0), gui = true) {
        if (can_auto_close) conclude()
        else {
          val button = new GUI.Button("Close") { override def clicked(): Unit = conclude() }
          set_actions(button)
          button.peer.getRootPane.setDefaultButton(button.peer)
        }
      }

    private def conclude(): Unit = {
      setVisible(false)
      dispose()
    }


    /* close */

    setDefaultCloseOperation(WindowConstants.DO_NOTHING_ON_CLOSE)

    addWindowListener(new WindowAdapter {
      override def windowClosing(e: WindowEvent): Unit = {
        if (_return_code.isDefined) conclude()
        else stopping()
      }
    })

    private def stopping(): Unit = {
      progress.stop()
      set_actions(new Label("Stopping ..."))
    }

    private val stop_button = new GUI.Button("Stop") {
      override def clicked(): Unit = stopping()
    }

    private var do_auto_close = true
    private def can_auto_close: Boolean = do_auto_close && _return_code == Some(0)

    private val auto_close = new GUI.Check("Auto close", init = do_auto_close) {
      tooltip = "Automatically close dialog when finished"
      override def clicked(state: Boolean): Unit = {
        do_auto_close = state
        if (can_auto_close) conclude()
      }
    }

    set_actions(stop_button, auto_close)


    /* main */

    setTitle("Isabelle build (" + PIDE.ml_settings.ml_identifier + " / " +
      "jdk-" + Platform.jvm_version + "_" + Platform.jvm_platform + ")")

    pack()
    setLocationRelativeTo(view)
    setVisible(true)

    Isabelle_Thread.fork(name = "session_build") {
      progress.echo("Build started for Isabelle/" +
        PIDE.resources.session_base.session_name + " ...")

      val (out, rc) =
        try { ("", JEdit_Session.session_build(progress)) }
        catch {
          case exn: Throwable =>
            (Output.error_message_text(Exn.message(exn)) + "\n", Exn.failure_rc(exn))
        }

      val ok = rc == Process_Result.RC.ok
      progress.echo(out + (if (ok) "OK" else Process_Result.RC.print_long(rc)) + "\n")

      if (ok) JEdit_Session.session_start()
      else progress.echo("Session build failed -- prover process remains inactive!")

      return_code(rc)
    }
  }
}
