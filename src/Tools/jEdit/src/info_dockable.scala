/*  Title:      Tools/jEdit/src/info_dockable.scala
    Author:     Makarius

Dockable window with info text.
*/

package isabelle.jedit


import isabelle._

import scala.actors.Actor._

import scala.swing.{FlowPanel, Button, CheckBox}
import scala.swing.event.ButtonClicked

import java.lang.System
import java.awt.BorderLayout
import java.awt.event.{ComponentEvent, ComponentAdapter}

import org.gjt.sp.jedit.View


object Info_Dockable
{
  /* implicit arguments -- owned by Swing thread */

  private var implicit_snapshot = Document.State.init.snapshot()
  private var implicit_info: XML.Body = Nil

  def apply(view: View, snapshot: Document.Snapshot, info: XML.Body)
  {
    Swing_Thread.require()

    implicit_snapshot = snapshot
    implicit_info = info

    view.getDockableWindowManager.floatDockableWindow("isabelle-info")

    implicit_snapshot = Document.State.init.snapshot()
    implicit_info = Nil
  }
}


class Info_Dockable(view: View, position: String) extends Dockable(view, position)
{
  Swing_Thread.require()


  /* component state -- owned by Swing thread */

  private var zoom_factor = 100


  /* pretty text area */

  private val pretty_text_area = new Pretty_Text_Area(view)
  set_content(pretty_text_area)

  pretty_text_area.update(Info_Dockable.implicit_snapshot, Info_Dockable.implicit_info)

  private def handle_resize()
  {
    Swing_Thread.require()

    pretty_text_area.resize(Isabelle.font_family(),
      scala.math.round(Isabelle.font_size("jedit_font_scale") * zoom_factor / 100))
  }


  /* main actor */

  private val main_actor = actor {
    loop {
      react {
        case Session.Global_Options =>
          Swing_Thread.later { handle_resize() }
        case bad => System.err.println("Info_Dockable: ignoring bad message " + bad)
      }
    }
  }

  override def init()
  {
    Swing_Thread.require()

    Isabelle.session.global_options += main_actor
    handle_resize()
  }

  override def exit()
  {
    Swing_Thread.require()

    Isabelle.session.global_options -= main_actor
    delay_resize.revoke()
  }


  /* resize */

  private val delay_resize =
    Swing_Thread.delay_first(
      Time.seconds(Isabelle.options.real("editor_update_delay"))) { handle_resize() }

  addComponentListener(new ComponentAdapter {
    override def componentResized(e: ComponentEvent) { delay_resize.invoke() }
  })


  /* controls */

  private val zoom = new Library.Zoom_Box(factor => { zoom_factor = factor; handle_resize() })
  zoom.tooltip = "Zoom factor for basic font size"

  private val controls = new FlowPanel(FlowPanel.Alignment.Right)(zoom)
  add(controls.peer, BorderLayout.NORTH)
}
