/*  Title:      Tools/jEdit/src/jedit_mouse_handler.scala
    Author:     Makarius

Mouse handler for EditPane in Isabelle/jEdit.
*/

package isabelle.jedit


import isabelle._

import java.awt.event.{MouseAdapter, MouseEvent}

import org.gjt.sp.jedit.{EditPane, EditPaneMouseHandlerFactory, Buffer}
import org.gjt.sp.jedit.textarea.{MouseHandler => JEditMouseHandler, TextAreaMouseHandler,
  JEditTextArea}


object JEdit_Mouse_Handler {
  class Factory extends EditPaneMouseHandlerFactory {
    override def create(edit_pane: EditPane): TextAreaMouseHandler =
      new JEdit_Mouse_Handler(edit_pane)
  }

  def jump_delay(options: Options): Time = options.seconds("editor_jump_delay")
  lazy val jump_delay0: Time = jump_delay(Options.init0())

  def jump_delay(): Time =
    PIDE.get_plugin match {
      case Some(plugin) => jump_delay(plugin.options.value)
      case None => jump_delay0
    }

  def jump(edit_pane: EditPane): Unit =
    if (edit_pane != null) {
      val text_area = edit_pane.getTextArea
      if (text_area != null) {
        Untyped.get[MouseAdapter](text_area, "mouseHandler") match {
          case mouse_handler: JEdit_Mouse_Handler => mouse_handler.jump()
          case _ =>
        }
      }
    }
}

class JEdit_Mouse_Handler(edit_pane: EditPane) extends JEditMouseHandler(edit_pane.getTextArea) {
  private var active_buffer: Buffer = null
  private var after_jump = false

  private val delay_jump =
    Delay.last(JEdit_Mouse_Handler.jump_delay(), gui = true) { after_jump = false }

  def jump(): Unit = { after_jump = true; delay_jump.invoke() }

  override def mousePressed(evt: MouseEvent): Unit = {
    active_buffer = edit_pane.getBuffer
    super.mousePressed(evt)
  }

  override def mouseDragged(evt: MouseEvent): Unit = {
    if (active_buffer == edit_pane.getBuffer && !after_jump) super.mouseDragged(evt)
  }

  override def mouseReleased(evt: MouseEvent): Unit = {
    val btn = evt.getButton
    if (btn == MouseEvent.BUTTON1 || btn == MouseEvent.BUTTON2 || btn == MouseEvent.BUTTON3) {
      if (active_buffer == edit_pane.getBuffer) super.mouseReleased(evt)
      else {
        dragged = false
        maybeDragAndDrop = false
      }
      active_buffer = null
    }
  }
}
