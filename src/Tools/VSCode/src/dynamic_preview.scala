/*  Title:      Tools/VSCode/src/dynamic_preview.scala
    Author:     Makarius

Dynamic preview, depending on caret document node.
*/

package isabelle.vscode


import isabelle._

import java.io.{File => JFile}


object Dynamic_Preview
{
  def make_preview(model: Document_Model, snapshot: Document.Snapshot): XML.Body =
    List(
      HTML.chapter("Preview " + model.node_name),
      HTML.itemize(
        snapshot.node.commands.toList.flatMap(
          command =>
            if (command.span.name == "") None
            else Some(HTML.text(command.span.name)))))

  object State
  {
    val init: State = State()
  }

  sealed case class State(file: Option[JFile] = None, body: XML.Body = Nil)
  {
    def handle_update(
      resources: VSCode_Resources,
      channel: Channel,
      changed: Option[Set[Document.Node.Name]]): State =
    {
      val st1 =
        if (resources.options.bool("vscode_caret_preview")) {
          resources.get_caret() match {
            case Some((caret_file, caret_model, _)) =>
              if (file != Some(caret_file) ||
                  changed.isDefined && changed.get.contains(caret_model.node_name))
              {
                val snapshot = caret_model.snapshot()
                if (!snapshot.is_outdated)
                  State(Some(caret_file), make_preview(caret_model, snapshot))
                else this
              }
              else this
            case None => State.init
          }
        }
        else State.init

      if (st1.body != body) {
        val content =
          if (st1.body.isEmpty) ""
          else HTML.output_document(Nil, st1.body, css = "")
        channel.write(Protocol.Dynamic_Preview(content))
      }

      st1
    }
  }

  def apply(server: Server): Dynamic_Preview = new Dynamic_Preview(server)
}


class Dynamic_Preview private(server: Server)
{
  private val state = Synchronized(Dynamic_Preview.State.init)

  private def handle_update(changed: Option[Set[Document.Node.Name]])
  { state.change(_.handle_update(server.resources, server.channel, changed)) }


  /* main */

  private val main =
    Session.Consumer[Any](getClass.getName) {
      case changed: Session.Commands_Changed => handle_update(Some(changed.nodes))
      case Session.Caret_Focus => handle_update(None)
    }

  def init()
  {
    server.session.commands_changed += main
    server.session.caret_focus += main
    handle_update(None)
  }

  def exit()
  {
    server.session.commands_changed -= main
    server.session.caret_focus -= main
  }
}
