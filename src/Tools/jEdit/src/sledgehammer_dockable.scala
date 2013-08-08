/*  Title:      Tools/jEdit/src/sledgehammer_dockable.scala
    Author:     Makarius

Dockable window for Sledgehammer.
*/

package isabelle.jedit


import isabelle._

import scala.actors.Actor._

import scala.swing.{FlowPanel, Button, Component, Label, TextField, CheckBox}
import scala.swing.event.ButtonClicked

import java.awt.BorderLayout
import java.awt.event.{ComponentEvent, ComponentAdapter, KeyEvent}

import org.gjt.sp.jedit.View
import org.gjt.sp.jedit.gui.HistoryTextField


class Sledgehammer_Dockable(view: View, position: String) extends Dockable(view, position)
{
  Swing_Thread.require()

  val pretty_text_area = new Pretty_Text_Area(view)
  set_content(pretty_text_area)


  /* query operation */

  private val sledgehammer =
    Query_Operation(view, "sledgehammer",
      (snapshot, results, body) =>
        pretty_text_area.update(snapshot, results, Pretty.separate(body)))


  /* resize */

  private var zoom_factor = 100

  private def handle_resize()
  {
    Swing_Thread.require()

    pretty_text_area.resize(Rendering.font_family(),
      (Rendering.font_size("jedit_font_scale") * zoom_factor / 100).round)
  }

  private val delay_resize =
    Swing_Thread.delay_first(PIDE.options.seconds("editor_update_delay")) { handle_resize() }

  addComponentListener(new ComponentAdapter {
    override def componentResized(e: ComponentEvent) { delay_resize.invoke() }
  })


  /* main actor */

  private val main_actor = actor {
    loop {
      react {
        case _: Session.Global_Options =>
          Swing_Thread.later { handle_resize() }
        case bad =>
          java.lang.System.err.println("Sledgehammer_Dockable: ignoring bad message " + bad)
      }
    }
  }

  override def init()
  {
    Swing_Thread.require()

    PIDE.session.global_options += main_actor
    handle_resize()
    sledgehammer.activate()
  }

  override def exit()
  {
    Swing_Thread.require()

    sledgehammer.deactivate()
    PIDE.session.global_options -= main_actor
    delay_resize.revoke()
  }


  /* controls */

  private def clicked {
    sledgehammer.apply_query(
      List(provers.getText, timeout.text, subgoal.text, isar_proofs.selected.toString))
  }

  private val provers_label = new Label("Provers: ") {
    tooltip = "Automatic provers as space-separated list (e.g. \"e spass remote_vampire\")"
  }

  private val provers = new HistoryTextField("isabelle-sledgehammer-provers") {
    setToolTipText(provers_label.tooltip)
    setColumns(20)
  }

  private val timeout = new TextField("30.0", 5) {
    tooltip = "Soft time limit for each automatic prover (seconds > 0)"
    verifier = (s: String) =>
      s match { case Properties.Value.Double(x) => x >= 0.0 case _ => false }
  }

  private val subgoal = new TextField("1", 5) {
    tooltip = "Subgoal number"
    verifier = (s: String) =>
      s match { case Properties.Value.Int(x) => x > 0 case _ => false }
  }

  private val isar_proofs = new CheckBox("Isar proofs") {
    tooltip = "Specify whether Isar proofs should be output in addition to metis line"
    selected = false
  }

  private val apply_query = new Button("Apply") {
    tooltip = "Search for first-order proof using automatic theorem provers"
    reactions += { case ButtonClicked(_) => clicked }
  }

  private val locate_query = new Button("Locate") {
    tooltip = "Locate context of current query within source text"
    reactions += { case ButtonClicked(_) => sledgehammer.locate_query() }
  }

  private val zoom = new GUI.Zoom_Box(factor => { zoom_factor = factor; handle_resize() }) {
    tooltip = "Zoom factor for output font size"
  }

  private val controls =
    new FlowPanel(FlowPanel.Alignment.Right)(
      provers_label, Component.wrap(provers), timeout, subgoal, isar_proofs,
      sledgehammer.animation, apply_query, locate_query, zoom)
  add(controls.peer, BorderLayout.NORTH)
}
