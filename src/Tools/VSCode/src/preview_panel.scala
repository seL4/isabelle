/*  Title:      Tools/VSCode/src/preview_panel.scala
    Author:     Makarius

HTML document preview.
*/

package isabelle.vscode


import isabelle._

import java.io.{File => JFile}


class Preview_Panel(resources: VSCode_Resources)
{
  private val pending = Synchronized(Map.empty[JFile, Int])

  def request(file: JFile, column: Int): Unit =
    pending.change(map => map + (file -> column))

  def flush(channel: Channel): Boolean =
  {
    pending.change_result(map =>
    {
      val map1 =
        (map /: map.iterator)({ case (m, (file, column)) =>
          resources.get_model(file) match {
            case Some(model) =>
              val snapshot = model.snapshot()
              if (snapshot.is_outdated) m
              else {
                val (label, content) = make_preview(model, snapshot)
                channel.write(Protocol.Preview_Response(file, column, label, content))
                m - file
              }
            case None => m - file
          }
        })
      (map1.nonEmpty, map1)
    })
  }

  def make_preview(model: Document_Model, snapshot: Document.Snapshot): (String, String) =
  {
    val label = "Preview " + quote(model.node_name.theory_base_name)
    val content =
      HTML.output_document(
        List(HTML.style(HTML.fonts_css()), HTML.style_file(HTML.isabelle_css)),
        List(HTML.source(Present.pide_document(snapshot))),
        css = "")
    (label, content)
  }
}
