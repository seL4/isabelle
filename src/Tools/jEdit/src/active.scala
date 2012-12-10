/*  Title:      Tools/jEdit/src/active.scala
    Author:     Makarius

Active areas within the document.
*/

package isabelle.jedit


import isabelle._

import org.gjt.sp.jedit.View


object Active
{
  def action(view: View, text: String, elem: XML.Elem)
  {
    Swing_Thread.require()

    Document_View(view.getTextArea) match {
      case Some(doc_view) =>
        doc_view.rich_text_area.robust_body() {
          val text_area = doc_view.text_area
          val model = doc_view.model
          val buffer = model.buffer
          val snapshot = model.snapshot()

          def try_replace_command(exec_id: Document.ID, s: String)
          {
            snapshot.state.execs.get(exec_id).map(_.command) match {
              case Some(command) =>
                snapshot.node.command_start(command) match {
                  case Some(start) =>
                    JEdit_Lib.buffer_edit(buffer) {
                      buffer.remove(start, command.proper_range.length)
                      buffer.insert(start, s)
                    }
                  case None =>
                }
              case None =>
            }
          }

          if (!snapshot.is_outdated) {
            elem match {
              case XML.Elem(Markup(Markup.SENDBACK, props), _) =>
                props match {
                  case Position.Id(exec_id) =>
                    try_replace_command(exec_id, text)
                  case _ =>
                    if (props.exists(_ == Markup.PADDING_LINE))
                      Isabelle.insert_line_padding(text_area, text)
                    else text_area.setSelectedText(text)
                }

              case XML.Elem(Markup(Markup.GRAPHVIEW, Position.Id(exec_id)), body) =>
                default_thread_pool.submit(() =>
                  {
                    val graph =
                      Exn.capture {
                        isabelle.graphview.Model.decode_graph(body)
                          .transitive_reduction_acyclic
                      }
                    Swing_Thread.later { Graphview_Dockable(view, snapshot, graph) }
                  })

              case _ =>
            }
          }
        }
      case None =>
    }
  }
}

