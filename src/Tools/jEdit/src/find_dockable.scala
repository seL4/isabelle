/*  Title:      Tools/jEdit/src/find_dockable.scala
    Author:     Makarius

Dockable window for "find" dialog.
*/

package isabelle.jedit


import isabelle._

import scala.actors.Actor._

import scala.swing.{Button, Component, TextField, CheckBox, Label, ComboBox}
import scala.swing.event.ButtonClicked

import java.awt.BorderLayout
import java.awt.event.{ComponentEvent, ComponentAdapter, KeyEvent}

import org.gjt.sp.jedit.View


class Find_Dockable(view: View, position: String) extends Dockable(view, position)
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
        process_indicator.update("Running find operation ...", 15)
      case Query_Operation.Status.FINISHED =>
        process_indicator.update(null, 0)
    }
  }

  private val find_theorems =
    new Query_Operation(PIDE.editor, view, "find_theorems", consume_status _,
      (snapshot, results, body) =>
        pretty_text_area.update(snapshot, results, Pretty.separate(body)))


  /* resize */

  private var zoom_factor = 100

  private def handle_resize()
  {
    Swing_Thread.require()

    pretty_text_area.resize(
      Font_Info.main(PIDE.options.real("jedit_font_scale") * zoom_factor / 100))
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
          System.err.println("Find_Dockable: ignoring bad message " + bad)
      }
    }
  }

  override def init()
  {
    PIDE.session.global_options += main_actor
    handle_resize()
    find_theorems.activate()
  }

  override def exit()
  {
    find_theorems.deactivate()
    PIDE.session.global_options -= main_actor
    delay_resize.revoke()
  }


  /* controls */

  private def clicked
  {
    find_theorems.apply_query(List(limit.text, allow_dups.selected.toString, query.getText))
  }

  private val query_label = new Label("Search criteria:") {
    tooltip =
      GUI.tooltip_lines(
        "Search criteria for find operation, e.g.\n\"_ = _\" \"op +\" name: Group -name: monoid")
  }

  private val query = new Completion_Popup.History_Text_Field("isabelle-find-theorems") {
    override def processKeyEvent(evt: KeyEvent)
    {
      if (evt.getID == KeyEvent.KEY_PRESSED && evt.getKeyCode == KeyEvent.VK_ENTER) clicked
      super.processKeyEvent(evt)
    }
    { val max = getPreferredSize; max.width = Integer.MAX_VALUE; setMaximumSize(max) }
    setColumns(40)
    setToolTipText(query_label.tooltip)
    setFont(GUI.imitate_font(Font_Info.main_family(), getFont, 1.2))
  }

  private val limit = new TextField(PIDE.options.int("find_theorems_limit").toString, 5) {
    tooltip = "Limit of displayed results"
    verifier = (s: String) =>
      s match { case Properties.Value.Int(x) => x >= 0 case _ => false }
  }

  private val allow_dups = new CheckBox("Duplicates") {
    tooltip = "Show all versions of matching theorems"
    selected = false
  }

  private val apply_query = new Button("Apply") {
    tooltip = "Find theorems meeting specified criteria"
    reactions += { case ButtonClicked(_) => clicked }
  }

  private val zoom = new GUI.Zoom_Box(factor => { zoom_factor = factor; handle_resize() }) {
    tooltip = "Zoom factor for output font size"
  }

  private val controls =
    new Wrap_Panel(Wrap_Panel.Alignment.Right)(
      query_label, Component.wrap(query), limit, allow_dups,
      process_indicator.component, apply_query, zoom)
  add(controls.peer, BorderLayout.NORTH)

  override def focusOnDefaultComponent { query.requestFocus }
}
