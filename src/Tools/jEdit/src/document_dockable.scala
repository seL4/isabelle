/*  Title:      Tools/jEdit/src/document_dockable.scala
    Author:     Makarius

Dockable window for document build support.
*/

package isabelle.jedit


import isabelle._

import java.awt.BorderLayout
import java.awt.event.{ComponentEvent, ComponentAdapter}

import scala.swing.{ComboBox, Button}
import scala.swing.event.{SelectionChanged, ButtonClicked}

import org.gjt.sp.jedit.{jEdit, View}


class Document_Dockable(view: View, position: String) extends Dockable(view, position) {
  GUI_Thread.require {}


  /* text area */

  val pretty_text_area = new Pretty_Text_Area(view)
  set_content(pretty_text_area)

  override def detach_operation: Option[() => Unit] = pretty_text_area.detach_operation


  /* document build process */

  private val process_indicator = new Process_Indicator


  /* resize */

  private val delay_resize =
    Delay.first(PIDE.options.seconds("editor_update_delay"), gui = true) { handle_resize() }

  addComponentListener(new ComponentAdapter {
    override def componentResized(e: ComponentEvent): Unit = delay_resize.invoke()
    override def componentShown(e: ComponentEvent): Unit = delay_resize.invoke()
  })

  private def handle_resize(): Unit =
    GUI_Thread.require { pretty_text_area.zoom(zoom.factor) }


  /* controls */

  private val document_session: ComboBox[String] = {
    new ComboBox(JEdit_Sessions.sessions_structure().build_topological_order.sorted) {
      val title = "Session"
      listenTo(selection)
      reactions += { case SelectionChanged(_) => }  // FIXME
    }
  }

  private val build_button = new Button("<html><b>Build</b></html>") {
      tooltip = "Build document"
      reactions += { case ButtonClicked(_) =>
        pretty_text_area.update(
          Document.Snapshot.init, Command.Results.empty,
            List(XML.Text(Date.now().toString)))  // FIXME
      }
    }

  private val zoom = new Font_Info.Zoom_Box { def changed(): Unit = handle_resize() }

  private val controls =
    Wrap_Panel(List(document_session, process_indicator.component, build_button,
      pretty_text_area.search_label, pretty_text_area.search_field, zoom))

  add(controls.peer, BorderLayout.NORTH)

  override def focusOnDefaultComponent(): Unit = build_button.requestFocus()


  /* main */

  private val main =
    Session.Consumer[Session.Global_Options](getClass.getName) {
      case _: Session.Global_Options =>
        GUI_Thread.later { handle_resize() }
    }

  override def init(): Unit = {
    PIDE.session.global_options += main
    handle_resize()
  }

  override def exit(): Unit = {
    PIDE.session.global_options -= main
    delay_resize.revoke()
  }
}

