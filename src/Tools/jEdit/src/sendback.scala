/*  Title:      Tools/jEdit/src/sendback.scala
    Author:     Makarius

Clickable "sendback" areas within the source text.
*/

package isabelle.jedit


import isabelle._

import org.gjt.sp.jedit.View


object Sendback
{
  def activate(view: View, text: String, props: Properties.T)
  {
    Swing_Thread.require()

    Document_View(view.getTextArea) match {
      case Some(doc_view) =>
        doc_view.rich_text_area.robust_body() {
          val text_area = doc_view.text_area
          val model = doc_view.model
          val buffer = model.buffer
          val snapshot = model.snapshot()

          if (!snapshot.is_outdated) {
            props match {
              case Position.Id(exec_id) =>
                snapshot.state.execs.get(exec_id).map(_.command) match {
                  case Some(command) =>
                    snapshot.node.command_start(command) match {
                      case Some(start) =>
                        JEdit_Lib.buffer_edit(buffer) {
                          buffer.remove(start, command.proper_range.length)
                          buffer.insert(start, text)
                        }
                      case None =>
                    }
                  case None =>
                }
              case _ =>
                if (props.exists(_ == Markup.PADDING_LINE))
                  Isabelle.insert_line_padding(text_area, text)
                else text_area.setSelectedText(text)
            }
          }
        }
      case None =>
    }
  }
}

