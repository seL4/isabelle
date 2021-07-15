/*  Title:      Tools/jEdit/src/sledgehammer_dockable.scala
    Author:     Makarius

Dockable window for Sledgehammer.
*/

package isabelle.jedit


import isabelle._

import scala.swing.{Button, Component, Label, CheckBox}
import scala.swing.event.ButtonClicked

import java.awt.BorderLayout
import java.awt.event.{ComponentEvent, ComponentAdapter, KeyEvent}

import org.gjt.sp.jedit.View
import org.gjt.sp.jedit.gui.HistoryTextField


class Sledgehammer_Dockable(view: View, position: String) extends Dockable(view, position)
{
  GUI_Thread.require {}


  /* text area */

  val pretty_text_area = new Pretty_Text_Area(view)
  set_content(pretty_text_area)

  override def detach_operation: Option[() => Unit] = pretty_text_area.detach_operation


  /* query operation */

  private val process_indicator = new Process_Indicator

  private def consume_status(status: Query_Operation.Status.Value): Unit =
  {
    status match {
      case Query_Operation.Status.WAITING =>
        process_indicator.update("Waiting for evaluation of context ...", 5)
      case Query_Operation.Status.RUNNING =>
        process_indicator.update("Sledgehammering ...", 15)
      case Query_Operation.Status.FINISHED =>
        process_indicator.update(null, 0)
    }
  }

  private val sledgehammer =
    new Query_Operation(PIDE.editor, view, "sledgehammer", consume_status,
      (snapshot, results, body) =>
        pretty_text_area.update(snapshot, results, Pretty.separate(body)))


  /* resize */

  private val delay_resize =
    Delay.first(PIDE.options.seconds("editor_update_delay"), gui = true) { handle_resize() }

  addComponentListener(new ComponentAdapter {
    override def componentResized(e: ComponentEvent): Unit = delay_resize.invoke()
    override def componentShown(e: ComponentEvent): Unit = delay_resize.invoke()
  })

  private def handle_resize(): Unit =
  {
    GUI_Thread.require {}

    pretty_text_area.resize(
      Font_Info.main(PIDE.options.real("jedit_font_scale") * zoom.factor / 100))
  }


  /* controls */

  private def clicked: Unit =
  {
    provers.addCurrentToHistory()
    PIDE.options.string("sledgehammer_provers") = provers.getText
    sledgehammer.apply_query(
      List(provers.getText, isar_proofs.selected.toString, try0.selected.toString))
  }

  private val provers_label = new Label("Provers:") {
    tooltip =
      GUI.tooltip_lines(
        "Automatic provers as space-separated list, e.g.\n" +
          PIDE.options.value.check_name("sledgehammer_provers").default_value)
  }

  private val provers = new HistoryTextField("isabelle-sledgehammer-provers") {
    override def processKeyEvent(evt: KeyEvent): Unit =
    {
      if (evt.getID == KeyEvent.KEY_PRESSED && evt.getKeyCode == KeyEvent.VK_ENTER) clicked
      super.processKeyEvent(evt)
    }
    setToolTipText(provers_label.tooltip)
    setColumns(30)
  }

  private def update_provers(): Unit =
  {
    val new_provers = PIDE.options.string("sledgehammer_provers")
    if (new_provers != provers.getText) {
      provers.setText(new_provers)
      if (provers.getCaret != null)
        provers.getCaret.setDot(0)
    }
  }

  private val isar_proofs = new CheckBox("Isar proofs") {
    tooltip = "Specify whether Isar proofs should be output in addition to \"by\" one-liner"
    selected = false
  }

  private val try0 = new CheckBox("Try methods") {
    tooltip = "Try standard proof methods like \"auto\" and \"blast\" as alternatives to \"metis\""
    selected = true
  }

  private val apply_query = new Button("<html><b>Apply</b></html>") {
    tooltip = "Search for first-order proof using automatic theorem provers"
    reactions += { case ButtonClicked(_) => clicked }
  }

  private val cancel_query = new Button("Cancel") {
    tooltip = "Interrupt unfinished sledgehammering"
    reactions += { case ButtonClicked(_) => sledgehammer.cancel_query() }
  }

  private val locate_query = new Button("Locate") {
    tooltip = "Locate context of current query within source text"
    reactions += { case ButtonClicked(_) => sledgehammer.locate_query() }
  }

  private val zoom = new Font_Info.Zoom_Box { def changed = handle_resize() }

  private val controls =
    Wrap_Panel(
      List(provers_label, Component.wrap(provers), isar_proofs, try0,
        process_indicator.component, apply_query, cancel_query, locate_query, zoom))

  add(controls.peer, BorderLayout.NORTH)

  override def focusOnDefaultComponent(): Unit = provers.requestFocus()


  /* main */

  private val main =
    Session.Consumer[Session.Global_Options](getClass.getName) {
      case _: Session.Global_Options => GUI_Thread.later { update_provers(); handle_resize() }
    }

  override def init(): Unit =
  {
    PIDE.session.global_options += main
    update_provers()
    handle_resize()
    sledgehammer.activate()
  }

  override def exit(): Unit =
  {
    sledgehammer.deactivate()
    PIDE.session.global_options -= main
    delay_resize.revoke()
  }
}
