/*  Title:      Tools/VSCode/extension/src/documentation_treeview.scala
    Author:     Fabian Huch

Isabelle documentation as a tree view.
*/

package isabelle.vscode.extension

import VSCode.{Event, Treeview, Uri, Window, Workspace, Commands, Language_Client}

import isabelle._
import isabelle.vscode._


object Documentation_Treeview {
  val name = "isabelle-documentation"
  val open_document_command = "isabelle.open-documentation"

  sealed case class Node(
    title: String,
    name: String = "",
    uri: Option[Uri] = None,
    important: Option[Boolean] = None,
    children: List[Node] = Nil
  )

  class Provider extends Treeview.Provider[Node] {
    private var _nodes: List[Node] = Nil
    private val _changed = new Event.Emitter[List[Node]]

    override val on_change = Some(_changed.event)

    def setup(language_client: Language_Client): Unit = {
      language_client.on_notification(LSP.Documentation_Response.name,
        { case LSP.Documentation_Response(contents) => update_nodes(contents.sections) })
      language_client.send_notification(LSP.Documentation_Request())
    }

    private def update_nodes(sections: List[Doc.Section]): Unit = {
      def map_entry(entry: Doc.Entry): Node = {
        Node(entry.title, name = entry.name, uri = Some(Uri.file(entry.path)))
      }
      def map_section(section: Doc.Section): Node = {
        Node(section.title, important = Some(section.important), children =
          section.entries.map(map_entry))
      }

      this._nodes = sections.map(map_section)
      this._changed.fire(Nil)
    }

    def get_children(element: Option[Node]): List[Node] = {
      element.map(_.children).getOrElse(_nodes)
    }

    def get_item(element: Node): Treeview.Item = {
      val label = if_proper(element.name.nonEmpty && element.title.nonEmpty, element.name + ":")

      def state(important: Option[Boolean]): Treeview.State =
        important match {
          case None => Treeview.State.none
          case Some(true) => Treeview.State.expanded
          case Some(false) => Treeview.State.collapsed
        }

      val item = state(element.important)

      val id =
        (if_proper(element.name.nonEmpty, element.name + if_proper(element.title, ": "))) +
          element.title
      val description =
        if (element.name.nonEmpty) (if (element.title.nonEmpty) element.title else element.name)
        else element.title

      element.uri match {
        case Some(uri) =>
          val command =
            Some(Commands.Command(
              command = open_document_command,
              title = "Open Documentation",
              arguments = List(uri)))
          Treeview.Item(label, item, id = id, description = description, uri = Some(uri),
            command = command)
        case None =>
          Treeview.Item(label, item, id = id, description = description, tooltip = element.title)
      }
    }

    def open_document(uri: Uri): Unit =
      if (File.is_pdf(uri.path)) Commands.execute("vscode.open", uri)
      else {
        for (document <- Workspace.open_document(uri))
        yield Window.show_document(document)
      }
  }
}
