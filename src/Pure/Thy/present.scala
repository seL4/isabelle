/*  Title:      Pure/Thy/present.scala
    Author:     Makarius

Theory presentation: HTML.
*/

package isabelle


import java.io.{File => JFile}

import scala.collection.immutable.SortedMap


object Present
{
  /* maintain chapter index -- NOT thread-safe */

  private val sessions_path = Path.basic(".sessions")

  private def read_sessions(dir: Path): List[(String, String)] =
  {
    val path = dir + sessions_path
    if (path.is_file) {
      import XML.Decode._
      list(pair(string, string))(Symbol.decode_yxml(File.read(path)))
    }
    else Nil
  }

  private def write_sessions(dir: Path, sessions: List[(String, String)])
  {
    import XML.Encode._
    File.write(dir + sessions_path, YXML.string_of_body(list(pair(string, string))(sessions)))
  }

  def update_chapter_index(browser_info: Path, chapter: String, new_sessions: List[(String, String)])
  {
    val dir = browser_info + Path.basic(chapter)
    Isabelle_System.mkdirs(dir)

    val sessions0 =
      try { read_sessions(dir) }
      catch { case _: XML.Error => Nil }

    val sessions = (SortedMap.empty[String, String] ++ sessions0 ++ new_sessions).toList
    write_sessions(dir, sessions)

    val title = "Isabelle/" + chapter + " sessions"
    HTML.write_document(dir, "index.html",
      List(HTML.title(title + " (" + Distribution.version + ")")),
      HTML.chapter(title) ::
       (if (sessions.isEmpty) Nil
        else
          List(HTML.div("sessions",
            List(HTML.description(
              sessions.map({ case (name, description) =>
                (List(HTML.link(name + "/index.html", HTML.text(name))),
                  if (description == "") Nil
                  else HTML.break ::: List(HTML.pre(HTML.text(description)))) })))))))
  }

  def make_global_index(browser_info: Path)
  {
    if (!(browser_info + Path.explode("index.html")).is_file) {
      Isabelle_System.mkdirs(browser_info)
      File.copy(Path.explode("~~/lib/logo/isabelle.gif"),
        browser_info + Path.explode("isabelle.gif"))
      File.write(browser_info + Path.explode("index.html"),
        File.read(Path.explode("~~/lib/html/library_index_header.template")) +
        File.read(Path.explode("~~/lib/html/library_index_content.template")) +
        File.read(Path.explode("~~/lib/html/library_index_footer.template")))
    }
  }


  /* finish session */

  def finish(
    progress: Progress,
    browser_info: Path,
    graph_file: JFile,
    info: Sessions.Info,
    name: String)
  {
    val session_prefix = browser_info + Path.basic(info.chapter) + Path.basic(name)
    val session_fonts = session_prefix + Path.explode("fonts")

    if (info.options.bool("browser_info")) {
      Isabelle_System.mkdirs(session_fonts)

      val session_graph = session_prefix + Path.basic("session_graph.pdf")
      File.copy(graph_file, session_graph.file)
      Isabelle_System.bash("chmod a+r " + File.bash_path(session_graph))

      HTML.write_isabelle_css(session_prefix)

      for (font <- Isabelle_System.fonts(html = true))
        File.copy(font, session_fonts)
    }
  }


  /* theory document */

  private val document_span_elements =
    Markup.Elements(Rendering.text_color.keySet + Markup.NUMERAL + Markup.COMMENT)

  def make_html(xml: XML.Body): XML.Body =
    xml map {
      case XML.Wrapped_Elem(markup, body1, body2) =>
        XML.Wrapped_Elem(markup, make_html(body1), make_html(body2))
      case XML.Elem(markup, body) =>
        val name = markup.name
        val html =
          markup.properties match {
            case Markup.Kind(kind) if kind == Markup.COMMAND || kind == Markup.KEYWORD =>
              List(HTML.span(kind, make_html(body)))
            case _ =>
              make_html(body)
          }
        Rendering.text_color.get(name) match {
          case Some(c) =>
            HTML.span(c.toString, html)
          case None =>
            if (document_span_elements(name)) HTML.span(name, html)
            else XML.Elem(markup, html)
        }
      case XML.Text(text) =>
        XML.Text(Symbol.decode(text))
    }

  def theory_document(snapshot: Document.Snapshot): XML.Body =
  {
    make_html(snapshot.markup_to_XML(Text.Range.full, document_span_elements))
  }
}
