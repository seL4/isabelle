/*  Title:      Tools/jEdit/src/info_dockable.scala
    Author:     Makarius

Dockable window with info text.
*/

package isabelle.jedit


import isabelle._

import java.awt.BorderLayout
import java.awt.event.{ComponentEvent, ComponentAdapter, WindowFocusListener, WindowEvent}

import org.gjt.sp.jedit.View


object Info_Dockable
{
  /* implicit arguments -- owned by GUI thread */

  private var implicit_snapshot = Document.Snapshot.init
  private var implicit_results = Command.Results.empty
  private var implicit_info: XML.Body = Nil

  private def set_implicit(
    snapshot: Document.Snapshot, results: Command.Results, info: XML.Body): Unit =
  {
    GUI_Thread.require {}

    implicit_snapshot = snapshot
    implicit_results = results
    implicit_info = info
  }

  private def reset_implicit(): Unit =
    set_implicit(Document.Snapshot.init, Command.Results.empty, Nil)

  def apply(
    view: View, snapshot: Document.Snapshot, results: Command.Results, info: XML.Body): Unit =
  {
    set_implicit(snapshot, results, info)
    view.getDockableWindowManager.floatDockableWindow("isabelle-info")
  }
}


class Info_Dockable(view: View, position: String) extends Dockable(view, position)
{
  /* component state -- owned by GUI thread */

  private val snapshot = Info_Dockable.implicit_snapshot
  private val results = Info_Dockable.implicit_results
  private val info = Info_Dockable.implicit_info

  private val window_focus_listener =
    new WindowFocusListener {
      def windowGainedFocus(e: WindowEvent): Unit =
        Info_Dockable.set_implicit(snapshot, results, info)
      def windowLostFocus(e: WindowEvent): Unit =
        Info_Dockable.reset_implicit()
    }


  /* pretty text area */

  private val pretty_text_area = new Pretty_Text_Area(view)
  set_content(pretty_text_area)

  pretty_text_area.update(snapshot, results, info)

  private val zoom = new Font_Info.Zoom_Box { def changed = handle_resize() }

  private def handle_resize(): Unit =
  {
    GUI_Thread.require {}

    pretty_text_area.resize(
      Font_Info.main(PIDE.options.real("jedit_font_scale") * zoom.factor / 100))
  }


  /* resize */

  private val delay_resize =
    Delay.first(PIDE.options.seconds("editor_update_delay"), gui = true) { handle_resize() }

  addComponentListener(new ComponentAdapter {
    override def componentResized(e: ComponentEvent): Unit = delay_resize.invoke()
    override def componentShown(e: ComponentEvent): Unit = delay_resize.invoke()
  })

  private val controls =
    Wrap_Panel(List(pretty_text_area.search_label, pretty_text_area.search_field, zoom))

  add(controls.peer, BorderLayout.NORTH)


  /* main */

  private val main =
    Session.Consumer[Session.Global_Options](getClass.getName) {
      case _: Session.Global_Options => GUI_Thread.later { handle_resize() }
    }

  override def init(): Unit =
  {
    GUI.parent_window(this).map(_.addWindowFocusListener(window_focus_listener))
    PIDE.session.global_options += main
    handle_resize()
  }

  override def exit(): Unit =
  {
    GUI.parent_window(this).map(_.removeWindowFocusListener(window_focus_listener))
    PIDE.session.global_options -= main
    delay_resize.revoke()
  }
}
