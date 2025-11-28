/*  Title:      Tools/jEdit/src/jedit_mouse_handler.scala
    Author:     Makarius

Mouse handler for EditPane in Isabelle/jEdit.
*/

package isabelle.jedit


import isabelle._

import org.gjt.sp.jedit.{EditPane, EditPaneMouseHandlerFactory}
import org.gjt.sp.jedit.textarea.{MouseHandler => JEditMouseHandler, TextAreaMouseHandler}


object JEdit_Mouse_Handler {
  class Factory extends EditPaneMouseHandlerFactory {
    override def create(edit_pane: EditPane): TextAreaMouseHandler =
      new JEdit_Mouse_Handler(edit_pane)
  }
}

class JEdit_Mouse_Handler(edit_pane: EditPane) extends JEditMouseHandler(edit_pane.getTextArea)
