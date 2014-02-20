/*  Title:      Tools/jEdit/src/info_dockable.scala
    Author:     Makarius

Dockable window with info text.
*/

package isabelle.jedit


import isabelle._

import scala.actors.Actor._

import scala.swing.Button
import scala.swing.event.ButtonClicked

import java.awt.BorderLayout
import java.awt.event.{ComponentEvent, ComponentAdapter, WindowFocusListener, WindowEvent}

import org.gjt.sp.jedit.View


object Info_Dockable
{
  /* implicit arguments -- owned by Swing thread */

  private var implicit_snapshot = Document.Snapshot.init
  private var implicit_results = Command.Results.empty
  private var implicit_info: XML.Body = Nil

  private def set_implicit(snapshot: Document.Snapshot, results: Command.Results, info: XML.Body)
  {
    Swing_Thread.require()

    implicit_snapshot = snapshot
    implicit_results = results
    implicit_info = info
  }

  private def reset_implicit(): Unit =
    set_implicit(Document.Snapshot.init, Command.Results.empty, Nil)

  def apply(view: View, snapshot: Document.Snapshot, results: Command.Results, info: XML.Body)
  {
    set_implicit(snapshot, results, info)
    view.getDockableWindowManager.floatDockableWindow("isabelle-info")
  }
}


class Info_Dockable(view: View, position: String) extends Dockable(view, position)
{
  /* component state -- owned by Swing thread */

  private var zoom_factor = 100

  private val snapshot = Info_Dockable.implicit_snapshot
  private val results = Info_Dockable.implicit_results
  private val info = Info_Dockable.implicit_info

  private val window_focus_listener =
    new WindowFocusListener {
      def windowGainedFocus(e: WindowEvent) { Info_Dockable.set_implicit(snapshot, results, info) }
      def windowLostFocus(e: WindowEvent) { Info_Dockable.reset_implicit() }
    }


  /* pretty text area */

  private val pretty_text_area = new Pretty_Text_Area(view)
  set_content(pretty_text_area)

  pretty_text_area.update(snapshot, results, info)

  private def handle_resize()
  {
    Swing_Thread.require()

    pretty_text_area.resize(Rendering.font_family(),
      (Rendering.font_size("jedit_font_scale") * zoom_factor / 100).round)
  }


  /* resize */

  private val delay_resize =
    Swing_Thread.delay_first(PIDE.options.seconds("editor_update_delay")) { handle_resize() }

  addComponentListener(new ComponentAdapter {
    override def componentResized(e: ComponentEvent) { delay_resize.invoke() }
  })

  private val zoom = new GUI.Zoom_Box(factor => { zoom_factor = factor; handle_resize() })
  zoom.tooltip = "Zoom factor for basic font size"

  private val controls = new Wrap_Panel(Wrap_Panel.Alignment.Right)(zoom)
  add(controls.peer, BorderLayout.NORTH)


  /* main actor */

  private val main_actor = actor {
    loop {
      react {
        case _: Session.Global_Options =>
          Swing_Thread.later { handle_resize() }

        case bad => System.err.println("Info_Dockable: ignoring bad message " + bad)
      }
    }
  }

  override def init()
  {
    GUI.parent_window(this).map(_.addWindowFocusListener(window_focus_listener))
    PIDE.session.global_options += main_actor
    handle_resize()
  }

  override def exit()
  {
    GUI.parent_window(this).map(_.removeWindowFocusListener(window_focus_listener))
    PIDE.session.global_options -= main_actor
    delay_resize.revoke()
  }
}
