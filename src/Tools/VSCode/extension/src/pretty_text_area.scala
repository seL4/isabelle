/*  Title:      Tools/VSCode/extension/pretty_text_area.scala
    Author:     Fabian Huch

GUI component for pretty-printed text with markup within Isabelle/VSCode.
*/

package isabelle.vscode.extension

import org.scalajs.dom

import isabelle._
import isabelle.vscode._


object Pretty_Text_Area {
  private val vscode = Webview_Api.acquire
  private val elements =
    Browser_Info.extra_elements.copy(entity = Markup.Elements.full,
      active = Language_Server.active_elements)

  private val node_context =
    new Browser_Info.Node_Context {
      override def make_ref(props: Properties.T, body: XML.Body): Option[XML.Elem] =
        for {
          json <-
            props match {
              case Position.Item_Def_File(file, line, offset) =>
                Some(LSP.Goto_Source_File(file, line, offset.start))
              case Position.Item_Def_Id(id, offset) =>
                Some(LSP.Goto_Command(id, offset.start))
              case _ => None
            }
        } yield {
          val script = Webview_Api.Post.function(JSON.Format(json))
          HTML.entity_ref(HTML.GUI.onclick(script)(HTML.link("#", body)))
        }

      override def make_file_ref(file: String, body: XML.Body): Option[XML.Elem] = {
        val script = Webview_Api.Post.function(JSON.Format(LSP.Goto_File(file)))
        Some(HTML.GUI.onclick(script)(HTML.link("#", body)))
      }

      override def make_active(active: XML.Elem, body: XML.Body): Option[XML.Elem] = {
        val msg = LSP.Markup_Action(active, XML.content(body))
        Some(HTML.class_("active")(
          HTML.GUI.onclick(Webview_Api.Post.function(JSON.Format(msg)))(HTML.span(body))))
      }
    }

  def make_html(formatted: XML.Body): XML.Body = node_context.make_html(elements, formatted)
}

class Pretty_Text_Area(
  on_update: XML.Body => Unit,
  container: dom.HTMLElement = dom.document.body
) {
  /* gui state */

  private var current_output: XML.Body = Nil
  private var current_metric: DOM_Metric = DOM_Metric()
  private var current_margin: Double = current_metric.content(container)
  private var resize_timeout: Option[Int] = None
  private var window_loaded = false


  /* update */

  def on_resize(): Unit =
    if (window_loaded) {
      resize_timeout.foreach(dom.window.clearTimeout)
      resize_timeout = Some(dom.window.setTimeout(() => handle_resize(), 50.0))
    }

  def on_load(): Unit = {
    current_metric = DOM_Metric()
    current_margin = current_metric.content(container)
    window_loaded = true
    update()
  }

  private def update(): Unit = {
    if (window_loaded) {
      val formatted =
        Pretty.formatted(Pretty.separate(current_output), margin = current_margin,
          metric = current_metric)
      on_update(List(HTML.source(Pretty_Text_Area.make_html(formatted))))
    }
  }

  def handle_update(output: XML.Body): Unit = {
    if (current_output != output) {
      current_output = output
      update()
    }
  }

  def handle_resize(): Unit = {
    val margin = current_metric.content(container)

    if (margin != current_margin) {
      current_margin = margin
      update()
    }
  }
}
