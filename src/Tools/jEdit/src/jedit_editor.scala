/*  Title:      Tools/jEdit/src/jedit_editor.scala
    Author:     Makarius

PIDE editor operations for jEdit.
*/

package isabelle.jedit


import isabelle._


import org.gjt.sp.jedit.{jEdit, View}


class JEdit_Editor extends Editor[View]
{
  def session: Session = PIDE.session

  def current_context: View =
    Swing_Thread.require { jEdit.getActiveView() }

  def current_node(view: View): Option[Document.Node.Name] =
    Swing_Thread.require { PIDE.document_model(view.getBuffer).map(_.node_name) }

  def current_snapshot(view: View): Option[Document.Snapshot] =
    Swing_Thread.require { PIDE.document_model(view.getBuffer).map(_.snapshot()) }

  def current_command(view: View, snapshot: Document.Snapshot): Option[(Command, Text.Offset)] =
  {
    Swing_Thread.require()

    if (snapshot.is_outdated) None
    else {
      val text_area = view.getTextArea
      PIDE.document_view(text_area) match {
        case Some(doc_view) =>
          val node = snapshot.version.nodes(doc_view.model.node_name)
          node.command_at(text_area.getCaretPosition)
        case None => None
      }
    }
  }
}
