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
    GUI_Thread.require {}

    Document_View(view.getTextArea) match {
      case Some(doc_view) =>
        doc_view.rich_text_area.robust_body() {
          val text_area = doc_view.text_area
          val model = doc_view.model
          val buffer = model.buffer
          val snapshot = model.snapshot()

          if (!snapshot.is_outdated) {
            // FIXME avoid hard-wired stuff
            elem match {
              case XML.Elem(Markup(Markup.BROWSER, _), body) =>
                Future.fork {
                  val graph_file = Isabelle_System.tmp_file("graph")
                  File.write(graph_file, XML.content(body))
                  Isabelle_System.bash_env(null,
                    Map("GRAPH_FILE" -> Isabelle_System.posix_path(graph_file)),
                    "\"$ISABELLE_TOOL\" browser -c \"$GRAPH_FILE\" &")
                }

              case XML.Elem(Markup(Markup.GRAPHVIEW, _), body) =>
                Future.fork {
                  val graph =
                    Exn.capture { Graph_Display.decode_graph(body).transitive_reduction_acyclic }
                  GUI_Thread.later { Graphview_Dockable(view, snapshot, graph) }
                }

              case XML.Elem(Markup(Markup.SIMP_TRACE_PANEL, props), _) =>
                val link =
                  props match {
                    case Position.Id(id) => PIDE.editor.hyperlink_command_id(snapshot, id)
                    case _ => None
                  }
                GUI_Thread.later {
                  link.foreach(_.follow(view))
                  view.getDockableWindowManager.showDockableWindow("isabelle-simplifier-trace")
                }

              case XML.Elem(Markup(Markup.SENDBACK, props), _) =>
                if (buffer.isEditable) {
                  props match {
                    case Position.Id(id) =>
                      Isabelle.edit_command(snapshot, buffer,
                        props.exists(_ == Markup.PADDING_COMMAND), id, text)
                    case _ =>
                      if (props.exists(_ == Markup.PADDING_LINE))
                        Isabelle.insert_line_padding(text_area, text)
                      else text_area.setSelectedText(text)
                  }
                  text_area.requestFocus
                }

              case Protocol.Dialog(id, serial, result) =>
                model.session.dialog_result(id, serial, result)

              case _ =>
            }
          }
        }
      case None =>
    }
  }
}
