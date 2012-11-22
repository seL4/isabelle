/*  Title:      Tools/jEdit/src/sendback.scala
    Author:     Makarius

Clickable "sendback" areas within the source text.
*/

package isabelle.jedit


import isabelle._

import org.gjt.sp.jedit.View


object Sendback
{
  def activate(view: View, text: String, id: Option[Document.Exec_ID])
  {
    Swing_Thread.require()

    Document_View(view.getTextArea) match {
      case Some(doc_view) =>
        doc_view.rich_text_area.robust_body() {
          val model = doc_view.model
          val buffer = model.buffer
          val snapshot = model.snapshot()

          if (!snapshot.is_outdated) {
            id match {
              case None =>
                doc_view.text_area.setSelectedText(text)
              case Some(exec_id) =>
                snapshot.state.execs.get(exec_id).map(_.command) match {
                  case Some(command) =>
                    snapshot.node.command_start(command) match {
                      case Some(start) =>
                        try {
                          buffer.beginCompoundEdit()
                          buffer.remove(start, command.proper_range.length)
                          buffer.insert(start, text)
                        }
                        finally {
                          buffer.endCompoundEdit()
                        }
                      case None =>
                    }
                  case None =>
                }
            }
          }
        }
      case None =>
    }
  }
}

