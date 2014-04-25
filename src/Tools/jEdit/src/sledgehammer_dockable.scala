/*  Title:      Tools/jEdit/src/sledgehammer_dockable.scala
    Author:     Makarius

Dockable window for Sledgehammer.
*/

package isabelle.jedit


import isabelle._

import scala.swing.{Button, Component, Label, TextField, CheckBox}
import scala.swing.event.ButtonClicked

import java.awt.BorderLayout
import java.awt.event.{ComponentEvent, ComponentAdapter, KeyEvent}

import org.gjt.sp.jedit.View
import org.gjt.sp.jedit.gui.HistoryTextField


class Sledgehammer_Dockable(view: View, position: String) extends Dockable(view, position)
{
  val pretty_text_area = new Pretty_Text_Area(view)
  set_content(pretty_text_area)


  /* query operation */

  private val process_indicator = new Process_Indicator

  private def consume_status(status: Query_Operation.Status.Value)
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
    new Query_Operation(PIDE.editor, view, "sledgehammer", consume_status _,
      (snapshot, results, body) =>
        pretty_text_area.update(snapshot, results, Pretty.separate(body)))


  /* resize */

  private var zoom_factor = 100

  private def handle_resize()
  {
    Swing_Thread.require {}

    pretty_text_area.resize(
      Font_Info.main(PIDE.options.real("jedit_font_scale") * zoom_factor / 100))
  }

  private val delay_resize =
    Swing_Thread.delay_first(PIDE.options.seconds("editor_update_delay")) { handle_resize() }

  addComponentListener(new ComponentAdapter {
    override def componentResized(e: ComponentEvent) { delay_resize.invoke() }
  })


  /* controls */

  private def clicked {
    PIDE.options.string("sledgehammer_provers") = provers.getText
    sledgehammer.apply_query(List(provers.getText, isar_proofs.selected.toString))
  }

  private val provers_label = new Label("Provers:") {
    tooltip =
      GUI.tooltip_lines(
        "Automatic provers as space-separated list, e.g.\ne spass remote_vampire")
  }

  private val provers = new HistoryTextField("isabelle-sledgehammer-provers") {
    override def processKeyEvent(evt: KeyEvent)
    {
      if (evt.getID == KeyEvent.KEY_PRESSED && evt.getKeyCode == KeyEvent.VK_ENTER) clicked
      super.processKeyEvent(evt)
    }
    setToolTipText(provers_label.tooltip)
    setColumns(30)
  }

  private def update_provers()
  {
    val new_provers = PIDE.options.string("sledgehammer_provers")
    if (new_provers != provers.getText) {
      provers.setText(new_provers)
      if (provers.getCaret != null)
        provers.getCaret.setDot(0)
    }
  }

  private val isar_proofs = new CheckBox("Isar proofs") {
    tooltip = "Specify whether Isar proofs should be output in addition to metis line"
    selected = false
  }

  private val apply_query = new Button("Apply") {
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

  private val zoom = new GUI.Zoom_Box(factor => { zoom_factor = factor; handle_resize() }) {
    tooltip = "Zoom factor for output font size"
  }

  private val controls =
    new Wrap_Panel(Wrap_Panel.Alignment.Right)(
      provers_label, Component.wrap(provers), isar_proofs,
      process_indicator.component, apply_query, cancel_query, locate_query, zoom)
  add(controls.peer, BorderLayout.NORTH)

  override def focusOnDefaultComponent { provers.requestFocus }


  /* main */

  private val main =
    Session.Consumer[Session.Global_Options](getClass.getName) {
      case _: Session.Global_Options => Swing_Thread.later { update_provers(); handle_resize() }
    }

  override def init()
  {
    PIDE.session.global_options += main
    update_provers()
    handle_resize()
    sledgehammer.activate()
  }

  override def exit()
  {
    sledgehammer.deactivate()
    PIDE.session.global_options -= main
    delay_resize.revoke()
  }
}
