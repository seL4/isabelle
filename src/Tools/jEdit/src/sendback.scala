/*  Title:      Tools/jEdit/src/sendback.scala
    Author:     Makarius

Clickable "sendback" areas within the source text.
*/

package isabelle.jedit


import isabelle._

import org.gjt.sp.jedit.{View, jEdit}
import org.gjt.sp.jedit.textarea.JEditTextArea


object Sendback
{
  def apply(command: Command, body: XML.Body): Sendback = new Sendback(command, body)
}

class Sendback private(command: Command, body: XML.Body)
{
  def activate(view: View)
  {
    Swing_Thread.require()

    Document_View(view.getTextArea) match {
      case Some(doc_view) =>
        doc_view.rich_text_area.robust_body() {
          val model = doc_view.model
          val buffer = model.buffer
          val snapshot = model.snapshot()
          snapshot.node.command_start(command) match {
            case Some(start) if !snapshot.is_outdated =>
              val text = Pretty.string_of(body)
              try {
                buffer.beginCompoundEdit()
                buffer.remove(start, command.proper_range.length)
                buffer.insert(start, text)
              }
              finally { buffer.endCompoundEdit() }
            case _ =>
          }
        }
      case None =>
    }
  }
}

