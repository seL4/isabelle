/*  Title:      Tools/jEdit/src/sendback.scala
    Author:     Makarius

Clickable "sendback" areas within the source text.
*/

package isabelle.jedit


import isabelle._

import org.gjt.sp.jedit.View


object Sendback
{
  def activate(view: View, text: String, exec_id: Document.Exec_ID)
  {
    Swing_Thread.require()

    Document_View(view.getTextArea) match {
      case Some(doc_view) =>
        doc_view.rich_text_area.robust_body() {
          val model = doc_view.model
          val buffer = model.buffer
          val snapshot = model.snapshot()

          snapshot.state.execs.get(exec_id).map(_.command) match {
            case Some(command) if !snapshot.is_outdated =>
              snapshot.node.command_start(command) match {
                case Some(start) =>
                  try {
                    buffer.beginCompoundEdit()
                    buffer.remove(start, command.proper_range.length)
                    buffer.insert(start, text)
                  }
                  finally { buffer.endCompoundEdit() }
                case None =>
              }
            case _ =>
          }
        }
      case None =>
    }
  }
}

