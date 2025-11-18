/*  Title:      Tools/jEdit/src/session_build.scala
    Author:     Makarius

Session build management.
*/

package isabelle.jedit


import isabelle._

import java.awt.Dimension
import java.awt.event.{WindowEvent, WindowAdapter}
import javax.swing.{WindowConstants, JDialog}
import javax.swing.text.{AttributeSet, StyleConstants}

import scala.swing.{ScrollPane, FlowPanel, BorderPanel, TextPane, Component, Label}

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

    private val text = new TextPane
    text.editable = false
    text.font = GUI.copy_font(GUI.label_font())
    text.caret.color = text.background
    text.preferredSize = {
      val metric = new Font_Metric(text.font)
      new Dimension((metric.average_width * 80).toInt, (metric.height * 25).toInt)
    }

    private val inverse: AttributeSet = {
      val style = text.styledDocument.addStyle("inverse", null)
      StyleConstants.setBackground(style, text.foreground)
      StyleConstants.setForeground(style, text.background)
      style
    }

    private val scroll_text = new ScrollPane(text)

    private def scroll_to_bottom(): Unit = GUI_Thread.later {
      val vertical = scroll_text.verticalScrollBar
      vertical.value = vertical.maximum
    }


    /* progress */

    private val progress = new Progress with Progress.Status {
      override def status_detailed: Boolean = true

      override def status_hide(msgs: Progress.Output): Unit = {
        val txt = output_text(msgs.map(Progress.output_theory), terminate = true)
        val m = txt.length
        if (m > 0) {
          GUI_Thread.later {
            val doc = text.styledDocument
            doc.remove(doc.getLength - m, m)
          }
        }
      }

      override def status_output(msgs: Progress.Output): Unit = {
        if (msgs.nonEmpty) {
          GUI_Thread.later {
            for (msg <- msgs) {
              val txt = output_text(List(Progress.output_theory(msg)), terminate = true)
              if (txt.nonEmpty) {
                val doc = text.styledDocument
                doc.insertString(doc.getLength, txt, if (msg.status) inverse else null)
              }
            }
            scroll_to_bottom()
          }
        }
      }
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
      progress.echo(Build.build_logic_started(PIDE.resources.session_base.session_name))

      val (out, rc) =
        try { ("", JEdit_Session.session_build(progress)) }
        catch {
          case exn: Throwable =>
            (Output.error_message_text(Exn.message(exn)) + "\n", Exn.failure_rc(exn))
        }

      val ok = rc == Process_Result.RC.ok
      progress.echo(out + (if (ok) "OK" else Process_Result.RC.print_long(rc)) + "\n")

      if (ok) JEdit_Session.session_start()
      else {
        progress.echo(
          Build.build_logic_failed(PIDE.resources.session_base.session_name, editor = true))
      }

      return_code(rc)
    }
  }
}
