/*  Title:      Tools/jEdit/src/debugger_dockable.scala
    Author:     Makarius

Dockable window for Isabelle/ML debugger.
*/

package isabelle.jedit


import isabelle._

import java.awt.BorderLayout
import java.awt.event.{ComponentEvent, ComponentAdapter}

import org.gjt.sp.jedit.View


class Debugger_Dockable(view: View, position: String) extends Dockable(view, position)
{
  GUI_Thread.require {}


  /* component state -- owned by GUI thread */

  private var current_snapshot = Document.Snapshot.init
  private var current_output: List[XML.Tree] = Nil


  /* pretty text area */

  val pretty_text_area = new Pretty_Text_Area(view)
  set_content(pretty_text_area)

  override def detach_operation = pretty_text_area.detach_operation


  private val zoom = new Font_Info.Zoom_Box { def changed = handle_resize() }

  private def handle_resize()
  {
    GUI_Thread.require {}

    pretty_text_area.resize(
      Font_Info.main(PIDE.options.real("jedit_font_scale") * zoom.factor / 100))
  }

  private def handle_update()
  {
    GUI_Thread.require {}

    val new_snapshot = PIDE.editor.current_node_snapshot(view).getOrElse(current_snapshot)
    val new_output = List(XML.Text("FIXME"))

    if (new_output != current_output)
      pretty_text_area.update(new_snapshot, Command.Results.empty, Pretty.separate(new_output))

    current_snapshot = new_snapshot
    current_output = new_output
  }


  /* main */

  private val main =
    Session.Consumer[Any](getClass.getName) {
      case _: Session.Global_Options =>
        GUI_Thread.later { handle_resize() }

      case Debugger.Event =>
        GUI_Thread.later { handle_update() }
    }

  override def init()
  {
    PIDE.session.global_options += main
    PIDE.session.debugger_events += main
    handle_update()
  }

  override def exit()
  {
    PIDE.session.global_options -= main
    PIDE.session.debugger_events -= main
    delay_resize.revoke()
  }


  /* resize */

  private val delay_resize =
    GUI_Thread.delay_first(PIDE.options.seconds("editor_update_delay")) { handle_resize() }

  addComponentListener(new ComponentAdapter {
    override def componentResized(e: ComponentEvent) { delay_resize.invoke() }
    override def componentShown(e: ComponentEvent) { delay_resize.invoke() }
  })


  /* controls */

  private val controls =
    new Wrap_Panel(Wrap_Panel.Alignment.Right)(
      pretty_text_area.search_label, pretty_text_area.search_field, zoom)
  add(controls.peer, BorderLayout.NORTH)
}
