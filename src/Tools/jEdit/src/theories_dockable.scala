/*  Title:      Tools/jEdit/src/theories_dockable.scala
    Author:     Makarius

Dockable window for theories managed by prover.
*/

package isabelle.jedit


import isabelle._

import scala.swing.{Button, TextArea, Label, ListView, ScrollPane, Component}

import java.awt.{BorderLayout, Graphics2D, Color, Point, Dimension}
import javax.swing.border.{BevelBorder, SoftBevelBorder}

import org.gjt.sp.jedit.{View, jEdit}


class Theories_Dockable(view: View, position: String) extends Dockable(view, position) {
  /* controls */

  def phase_text(phase: Session.Phase): String = "Prover: " + phase.print

  private val session_phase = new Label(phase_text(PIDE.session.phase))
  session_phase.border = new SoftBevelBorder(BevelBorder.LOWERED)
  session_phase.tooltip = "Status of prover session"

  private def handle_phase(phase: Session.Phase): Unit = GUI_Thread.require {
    session_phase.text = " " + phase_text(phase) + " "
  }

  private val purge = new GUI.Button("Purge") {
    tooltip = "Remove theories that are no longer required"
    override def clicked(): Unit = PIDE.editor.purge()
  }

  private val continuous_checking = new JEdit_Options.continuous_checking.GUI
  continuous_checking.focusable = false

  private val logic = JEdit_Sessions.logic_selector(PIDE.options, standalone = true)
  private val skip_proofs = new JEdit_Options.skip_proofs.GUI
  skip_proofs.focusable = false

  private val defer_proofs = new JEdit_Options.defer_proofs.GUI
  defer_proofs.focusable = false

  private val quick_print = new JEdit_Options.quick_print.GUI
  quick_print.focusable = false

  private val controls =
    Wrap_Panel(List(purge, skip_proofs, defer_proofs, quick_print, continuous_checking, session_phase, logic))

  add(controls.peer, BorderLayout.NORTH)


  /* main */

  private val theories = new Theories_Status(view)
  set_content(new ScrollPane(theories.gui))

  private val main =
    Session.Consumer[Any](getClass.getName) {
      case phase: Session.Phase =>
        GUI_Thread.later { handle_phase(phase) }

      case _: Session.Global_Options =>
        GUI_Thread.later {
          skip_proofs.load()
          defer_proofs.load()
          quick_print.load()
          continuous_checking.load()
          logic.load()
          theories.refresh()
        }

      case changed: Session.Commands_Changed =>
        GUI_Thread.later { theories.update(domain = Some(changed.nodes), trim = changed.assignment) }
    }

  override def init(): Unit = {
    PIDE.session.phase_changed += main
    PIDE.session.global_options += main
    PIDE.session.commands_changed += main

    handle_phase(PIDE.session.phase)
    theories.update()
  }

  override def exit(): Unit = {
    PIDE.session.phase_changed -= main
    PIDE.session.global_options -= main
    PIDE.session.commands_changed -= main
  }
}
