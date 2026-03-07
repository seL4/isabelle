/*  Title:      Tools/jEdit/src/active.scala
    Author:     Makarius

Active areas within the document.
*/

package isabelle.jedit


import isabelle._
import org.gjt.sp.jedit.{ServiceManager, View}


object Active {
  abstract class Handler {
    def handle(
      editor_context: JEdit_Editor.Context, text: String, elem: XML.Elem,
      doc_view: Document_View, snapshot: Document.Snapshot): Boolean
  }

  def handlers: List[Handler] =
    ServiceManager.getServiceNames(classOf[Handler]).toList
      .map(ServiceManager.getService(classOf[Handler], _))

  def action(editor_context: JEdit_Editor.Context, text: String, elem: XML.Elem): Unit = {
    GUI_Thread.require {}

    Document_View.get(editor_context.text_area) match {
      case Some(doc_view) =>
        doc_view.rich_text_area.robust_body(()) {
          val snapshot = Document_Model.snapshot(doc_view.model)
          if (!snapshot.is_outdated) {
            handlers.find(_.handle(editor_context, text, elem, doc_view, snapshot))
          }
        }
      case None =>
    }
  }

  class Misc_Handler extends Active.Handler {
    override def handle(
      editor_context: JEdit_Editor.Context, text: String, elem: XML.Elem,
      doc_view: Document_View, snapshot: Document.Snapshot
    ): Boolean = {
      val view = editor_context.view
      val text_area = doc_view.text_area
      val model = doc_view.model
      val buffer = model.buffer

      elem match {
        case XML.Elem(Markup(Markup.BROWSER, _), body) =>
          Isabelle_Thread.fork(name = "browser") {
            val graph_file = Isabelle_System.tmp_file("graph")
            File.write(graph_file, XML.content(body))
            Isabelle_System.bash("isabelle browser -c " + File.bash_path(graph_file) + " &")
          }
          true

        case XML.Elem(Markup(Markup.THEORY_EXPORTS, props), _) =>
          GUI_Thread.later {
            val name = Markup.Name.unapply(props) getOrElse ""
            JEdit_Editor.hyperlink_file(Isabelle_Export.vfs_prefix + name, focus = true)
              .follow(editor_context)
          }
          true

        case XML.Elem(Markup(Markup.JEDIT_ACTION, _), body) =>
          GUI_Thread.later {
            view.getInputHandler.invokeAction(XML.content(body))
          }
          true

        case XML.Elem(Markup(Markup.SIMP_TRACE_PANEL, props), _) =>
          val link =
            props match {
              case Position.Id(id) => JEdit_Editor.hyperlink_command(snapshot, id, focus = true)
              case _ => None
            }
          GUI_Thread.later {
            link.foreach(_.follow(editor_context))
            view.getDockableWindowManager.showDockableWindow("isabelle-simplifier-trace")
          }
          true

        case XML.Elem(Markup(Markup.SENDBACK, props), _) =>
          if (buffer.isEditable) {
            props match {
              case Position.Id(id) =>
                Isabelle.edit_command(snapshot, text_area,
                  props.contains(Markup.PADDING_COMMAND), id, text)
              case _ =>
                if (props.contains(Markup.PADDING_LINE)) {
                  Isabelle.insert_line_padding(text_area, text)
                }
                else text_area.setSelectedText(text)
            }
            text_area.requestFocus()
          }
          true

        case Protocol.Dialog(id, serial, result) =>
          model.session.dialog_result(id, serial, result)
          true

        case _ => false
      }
    }
  }
}
