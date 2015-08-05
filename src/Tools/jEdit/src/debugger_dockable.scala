/*  Title:      Tools/jEdit/src/debugger_dockable.scala
    Author:     Makarius

Dockable window for Isabelle/ML debugger.
*/

package isabelle.jedit


import isabelle._

import java.awt.BorderLayout
import java.awt.event.{ComponentEvent, ComponentAdapter, KeyEvent}

import scala.swing.{Button, Label, Component}
import scala.swing.event.ButtonClicked

import org.gjt.sp.jedit.View


class Debugger_Dockable(view: View, position: String) extends Dockable(view, position)
{
  GUI_Thread.require {}


  /* component state -- owned by GUI thread */

  private var current_snapshot = Document.Snapshot.init
  private var current_output: List[XML.Tree] = Nil


  /* common GUI components */

  private val context_label = new Label("Context:") { tooltip = "Isabelle/ML context (optional)" }
  private val context_field =
    new Completion_Popup.History_Text_Field("isabelle-debugger-context")
    {
      setColumns(20)
      setToolTipText(context_label.tooltip)
      setFont(GUI.imitate_font(getFont, Font_Info.main_family(), 1.2))
    }

  private val expression_label = new Label("ML:") { tooltip = "Isabelle/ML expression" }
  private val expression_field =
    new Completion_Popup.History_Text_Field("isabelle-debugger-expression")
    {
      override def processKeyEvent(evt: KeyEvent)
      {
        if (evt.getID == KeyEvent.KEY_PRESSED && evt.getKeyCode == KeyEvent.VK_ENTER)
          eval_expression()
        super.processKeyEvent(evt)
      }
      { val max = getPreferredSize; max.width = Integer.MAX_VALUE; setMaximumSize(max) }
      setColumns(40)
      setToolTipText(expression_label.tooltip)
      setFont(GUI.imitate_font(getFont, Font_Info.main_family(), 1.2))
    }

  private val eval_button = new Button("<html><b>Eval</b></html>") {
      tooltip = "Evaluate Isabelle/ML expression within optional context"
      reactions += { case ButtonClicked(_) => eval_expression() }
    }

  private def eval_expression()
  {
    // FIXME
    Output.writeln("eval context = " + quote(context_field.getText) + " expression = " +
      quote(expression_field.getText))
  }

  private val zoom = new Font_Info.Zoom_Box { def changed = handle_resize() }


  /* pretty text area */

  val pretty_text_area = new Pretty_Text_Area(view)
  set_content(pretty_text_area)

  override def detach_operation = pretty_text_area.detach_operation


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
    val new_output =  // FIXME select by thread name
      (for ((_, results) <- Debugger.current_state.output; (_, tree) <- results.iterator)
        yield tree).toList ::: List(XML.Text(Debugger.current_state.threads.toString))

    if (new_output != current_output)
      pretty_text_area.update(new_snapshot, Command.Results.empty, Pretty.separate(new_output))

    current_snapshot = new_snapshot
    current_output = new_output
  }


  /* main */

  private val main =
    Session.Consumer[Any](getClass.getName) {
      case _: Session.Global_Options =>
        Debugger.init(PIDE.session)
        GUI_Thread.later { handle_resize() }

      case _: Debugger.Update =>
        GUI_Thread.later { handle_update() }
    }

  override def init()
  {
    PIDE.session.global_options += main
    PIDE.session.debugger_updates += main
    Debugger.init(PIDE.session)
    handle_update()
  }

  override def exit()
  {
    PIDE.session.global_options -= main
    PIDE.session.debugger_updates -= main
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
      context_label, Component.wrap(context_field),
      expression_label, Component.wrap(expression_field), eval_button,
      pretty_text_area.search_label, pretty_text_area.search_field, zoom)
  add(controls.peer, BorderLayout.NORTH)
}
