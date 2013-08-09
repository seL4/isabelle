/*  Title:      Tools/jEdit/src/find_dockable.scala
    Author:     Makarius

Dockable window for "find" dialog.
*/

package isabelle.jedit


import isabelle._

import scala.actors.Actor._

import scala.swing.{FlowPanel, Button, Component}
import scala.swing.event.ButtonClicked

import java.awt.BorderLayout
import java.awt.event.{ComponentEvent, ComponentAdapter, KeyEvent}

import org.gjt.sp.jedit.View
import org.gjt.sp.jedit.gui.HistoryTextField


class Find_Dockable(view: View, position: String) extends Dockable(view, position)
{
  Swing_Thread.require()

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
    Query_Operation(view, "find_theorems", consume_status _,
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
          java.lang.System.err.println("Find_Dockable: ignoring bad message " + bad)
      }
    }
  }

  override def init()
  {
    Swing_Thread.require()

    PIDE.session.global_options += main_actor
    handle_resize()
    find_theorems.activate()
  }

  override def exit()
  {
    Swing_Thread.require()

    find_theorems.deactivate()
    PIDE.session.global_options -= main_actor
    delay_resize.revoke()
  }


  /* controls */

  private def clicked { find_theorems.apply_query(List(query.getText)) }

  private val query = new HistoryTextField("isabelle-find-theorems") {
    override def processKeyEvent(evt: KeyEvent)
    {
      if (evt.getID == KeyEvent.KEY_PRESSED && evt.getKeyCode == KeyEvent.VK_ENTER) clicked
      super.processKeyEvent(evt)
    }
    { val max = getPreferredSize; max.width = Integer.MAX_VALUE; setMaximumSize(max) }
    setColumns(40)
  }

  private val query_wrapped = Component.wrap(query)

  private val apply_query = new Button("Apply") {
    tooltip = "Find theorems meeting specified criteria"
    reactions += { case ButtonClicked(_) => clicked }
  }

  private val locate_query = new Button("Locate") {
    tooltip = "Locate context of current query within source text"
    reactions += { case ButtonClicked(_) => find_theorems.locate_query() }
  }

  private val zoom = new GUI.Zoom_Box(factor => { zoom_factor = factor; handle_resize() }) {
    tooltip = "Zoom factor for output font size"
  }

  private val controls =
    new FlowPanel(FlowPanel.Alignment.Right)(
      query_wrapped, process_indicator.component, apply_query, locate_query, zoom)
  add(controls.peer, BorderLayout.NORTH)
}
