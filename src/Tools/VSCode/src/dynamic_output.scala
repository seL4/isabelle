/*  Title:      Tools/VSCode/src/dynamic_output.scala
    Author:     Makarius

Dynamic output, depending on caret focus: messages, state etc.
*/

package isabelle.vscode


import isabelle._


object Dynamic_Output {
  sealed case class State(do_update: Boolean = true, output: List[XML.Tree] = Nil) {
    def handle_update(
      resources: VSCode_Resources,
      channel: Channel,
      restriction: Option[Set[Command]],
      html_output: Boolean,
      margin: Double,
      force: Boolean,
    ): State = {
      val st1 =
        resources.get_caret() match {
          case None => copy(output = Nil)
          case Some(caret) =>
            val snapshot = resources.snapshot(caret.model)
            if (do_update && !snapshot.is_outdated) {
              snapshot.current_command(caret.node_name, caret.offset) match {
                case None => copy(output = Nil)
                case Some(command) =>
                  copy(output =
                    if (restriction.isEmpty || restriction.get.contains(command)) {
                      val output_state = resources.options.bool("editor_output_state")
                      Rendering.output_messages(snapshot.command_results(command), output_state)
                    } else output)
              }
            }
            else this
        }
      if (st1.output != output || force) {
        if (html_output) {
          val node_context =
            new Browser_Info.Node_Context {
              override def make_ref(props: Properties.T, body: XML.Body): Option[XML.Elem] =
                for {
                  thy_file <- Position.Def_File.unapply(props)
                  def_line <- Position.Def_Line.unapply(props)
                  source <- resources.source_file(thy_file)
                  uri = File.uri(Path.explode(source).absolute_file)
                } yield HTML.link(uri.toString + "#" + def_line, body)
            }
          val elements = Browser_Info.extra_elements.copy(entity = Markup.Elements.full)
          val separate = Pretty.separate(st1.output)
          val formatted = Pretty.formatted(separate, margin = margin)
          val html = node_context.make_html(elements, formatted)
          channel.write(LSP.Dynamic_Output(HTML.source(html).toString))
        } else {
          val separate = Pretty.separate(st1.output)
          val formatted = Pretty.formatted(separate, margin = margin)
          val tree = Markup_Tree.from_XML(formatted)

          val output = resources.output_pretty(separate, margin = margin)

          val document = Line.Document(output)
          val decorations = tree
            .cumulate(Text.Range.full, None: Option[String], Rendering.text_color_elements, (_, m) => {
              Some(Some(m.info.name))
            })
            .flatMap(e => e._2 match {
              case None => None
              case Some(i) => Some((document.range(e._1), "text_" ++ Rendering.text_color(i).toString))
            })
            .groupMap(_._2)(e => LSP.Decoration_Options(e._1, List())).toList

          channel.write(LSP.Dynamic_Output(output, Some(decorations)))
        }
      }
      st1
    }
  }

  def apply(server: Language_Server): Dynamic_Output = new Dynamic_Output(server)
}


class Dynamic_Output private(server: Language_Server) {
  private val state = Synchronized(Dynamic_Output.State())
  private val margin_ = Synchronized(None: Option[Double])
  def margin: Double = margin_.value.getOrElse(server.resources.message_margin)

  private def handle_update(restriction: Option[Set[Command]], force: Boolean = false): Unit = {
    val html_output = server.resources.html_output
    state.change(
      _.handle_update(server.resources, server.channel, restriction, html_output, margin, force))
  }


  /* main */

  private val main =
    Session.Consumer[Any](getClass.getName) {
      case changed: Session.Commands_Changed =>
        handle_update(if (changed.assignment) None else Some(changed.commands))

      case Session.Caret_Focus =>
        handle_update(None)
    }

  def init(): Unit = {
    server.session.commands_changed += main
    server.session.caret_focus += main
    handle_update(None)
  }

  def exit(): Unit = {
    server.session.commands_changed -= main
    server.session.caret_focus -= main
  }

  def set_margin(margin: Double): Unit = {
    margin_.change(_ => Some(margin))
    handle_update(None, force = true)
  }
}
