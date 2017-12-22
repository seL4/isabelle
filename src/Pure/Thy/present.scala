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


  /** preview **/

  sealed case class Preview(title: String, content: String)

  def preview(snapshot: Document.Snapshot,
    plain_text: Boolean = false,
    fonts_url: String => String = HTML.fonts_url()): Preview =
  {
    require(!snapshot.is_outdated)

    def output_document(title: String, body: XML.Body): String =
      HTML.output_document(
        List(
          HTML.style(HTML.fonts_css(fonts_url) + File.read(HTML.isabelle_css)),
          HTML.title(title)),
        List(HTML.source(body)), css = "")

    val name = snapshot.node_name
    if (plain_text) {
      val title = "File " + quote(name.path.base_name)
      val content = output_document(title, HTML.text(snapshot.node.source))
      Preview(title, content)
    }
    else if (name.is_bibtex) {
      val title = "Bibliography " + quote(name.path.base_name)
      val content =
        Isabelle_System.with_tmp_file("bib", "bib") { bib =>
          File.write(bib, snapshot.node.source)
          Bibtex.html_output(List(bib), style = "unsort", title = title)
        }
      Preview(title, content)
    }
    else {
      val title =
        if (name.is_theory) "Theory " + quote(name.theory_base_name)
        else "File " + quote(name.path.base_name)
      val content = output_document(title, pide_document(snapshot))
      Preview(title, content)
    }
  }


  /* PIDE document */

  private val document_span_elements =
    Rendering.foreground_elements ++ Rendering.text_color_elements + Markup.NUMERAL + Markup.COMMENT

  private def make_html(xml: XML.Body): XML.Body =
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
        Rendering.foreground.get(name) orElse Rendering.text_color.get(name) match {
          case Some(c) => HTML.span(c.toString, html)
          case None => HTML.span(name, html)
        }
      case XML.Text(text) =>
        XML.Text(Symbol.decode(text))
    }

  def pide_document(snapshot: Document.Snapshot): XML.Body =
    make_html(snapshot.markup_to_XML(Text.Range.full, document_span_elements))



  /** build document **/

  val default_document_name = "document"
  val default_document_format = "pdf"
  val document_formats = List("pdf", "dvi")
  def default_document_dir(name: String): Path = Path.explode("output") + Path.basic(name)

  def document_tags(tags: List[String]): String =
  {
    cat_lines(
      tags.map(tag =>
        tag.toList match {
          case '/' :: cs => "\\isafoldtag{" + cs.mkString + "}"
          case '-' :: cs => "\\isadroptag{" + cs.mkString + "}"
          case '+' :: cs => "\\isakeeptag{" + cs.mkString + "}"
          case cs => "\\isakeeptag{" + cs.mkString + "}"
        })) + "\n"
  }

  def build_document(
    document_name: String = default_document_name,
    document_format: String = default_document_format,
    document_dir: Option[Path] = None,
    tags: List[String] = Nil)
  {
    val document_target = Path.parent + Path.explode(document_name).ext(document_format)

    if (!document_formats.contains(document_format))
      error("Bad document output format: " + quote(document_format))

    val dir = document_dir getOrElse default_document_dir(document_name)
    if (!dir.is_dir) error("Bad document output directory " + dir)

    val root_name =
    {
      val root1 = "root_" + document_name
      if ((dir + Path.explode(root1).ext("tex")).is_file) root1 else "root"
    }


    /* bash scripts */

    def root_bash(ext: String): String = Bash.string(root_name + "." + ext)

    def latex_bash(fmt: String, ext: String = "tex"): String =
      "isabelle latex -o " + Bash.string(fmt) + " " + Bash.string(root_name + "." + ext)

    def bash(script: String): Process_Result =
      Isabelle_System.bash(script, cwd = dir.file)


    /* prepare document */

    File.write(dir + Path.explode("isabelletags.sty"), document_tags(tags))

    List("log", "blg").foreach(ext => (dir + Path.explode(root_name).ext(ext)).file.delete)

    val result =
      if ((dir + Path.explode("build")).is_file) {
        bash("./build " + Bash.string(document_format) + " " + Bash.string(document_name))
      }
      else {
        bash(
          List(
            latex_bash("sty"),
            latex_bash(document_format),
            "{ [ ! -f " + root_bash("bib") + " ] || " + latex_bash("bbl") + "; }",
            "{ [ ! -f " + root_bash("idx") + " ] || " + latex_bash("idx") + "; }",
            latex_bash(document_format),
            latex_bash(document_format)).mkString(" && "))
      }


    /* result */

    if (!result.ok) {
      cat_error(
        cat_lines(Latex.latex_errors(dir, root_name) ::: Bibtex.bibtex_errors(dir, root_name)),
        "Failed to build document in " + File.path(dir.absolute_file))
    }

    bash("[ -f " + root_bash(document_format) + " ] && cp -f " +
      root_bash(document_format) + " " + File.bash_path(document_target)).check
  }


  /* Isabelle tool wrapper */

  val isabelle_tool =
    Isabelle_Tool("document", "prepare theory session document", args =>
  {
    var document_dir: Option[Path] = None
    var document_name = default_document_name
    var document_format = default_document_format
    var tags: List[String] = Nil

    val getopts = Getopts("""
Usage: isabelle document [OPTIONS]

  Options are:
    -d DIR       document output directory (default """ +
      default_document_dir(default_document_name) + """)
    -n NAME      document name (default """ + quote(default_document_name) + """)
    -o FORMAT    document format: """ +
      commas(document_formats.map(fmt =>
        fmt + (if (fmt == default_document_format) " (default)" else ""))) + """
    -t TAGS      markup for tagged regions

  Prepare the theory session document in document directory, producing the
  specified output format.
""",
      "d:" -> (arg => document_dir = Some(Path.explode(arg))),
      "n:" -> (arg => document_name = arg),
      "o:" -> (arg => document_format = arg),
      "t:" -> (arg => tags = space_explode(',', arg)))

    val more_args = getopts(args)
    if (more_args.nonEmpty) getopts.usage()

    try {
      build_document(document_dir = document_dir, document_name = document_name,
        document_format = document_format, tags = tags)
    }
    catch { case ERROR(msg) => Output.writeln(msg); sys.exit(1) }
  })
}
