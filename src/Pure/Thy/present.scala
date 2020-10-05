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
    val dir = Isabelle_System.make_directory(browser_info + Path.basic(chapter))

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
                val descr = Symbol.trim_blank_lines(description)
                (List(HTML.link(name + "/index.html", HTML.text(name))),
                  if (descr == "") Nil
                  else HTML.break ::: List(HTML.pre(HTML.text(descr)))) })))))))
  }

  def make_global_index(browser_info: Path)
  {
    if (!(browser_info + Path.explode("index.html")).is_file) {
      Isabelle_System.make_directory(browser_info)
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
      Isabelle_System.make_directory(session_fonts)

      val session_graph = session_prefix + Path.basic("session_graph.pdf")
      File.copy(graph_file, session_graph.file)
      Isabelle_System.chmod("a+r", session_graph)

      HTML.write_isabelle_css(session_prefix)

      for (entry <- Isabelle_Fonts.fonts(hidden = true))
        File.copy(entry.path, session_fonts)
    }
  }


  /** preview **/

  sealed case class Preview(title: String, content: String)

  def preview(
    resources: Resources,
    snapshot: Document.Snapshot,
    plain_text: Boolean = false,
    fonts_url: String => String = HTML.fonts_url()): Preview =
  {
    require(!snapshot.is_outdated)

    def output_document(title: String, body: XML.Body): String =
      HTML.output_document(
        List(
          HTML.style(HTML.fonts_css(fonts_url) + "\n\n" + File.read(HTML.isabelle_css)),
          HTML.title(title)),
        List(HTML.source(body)), css = "", structural = false)

    val name = snapshot.node_name

    if (plain_text) {
      val title = "File " + quote(name.path.file_name)
      val content = output_document(title, HTML.text(snapshot.node.source))
      Preview(title, content)
    }
    else {
      resources.make_preview(snapshot) match {
        case Some(preview) => preview
        case None =>
          val title =
            if (name.is_theory) "Theory " + quote(name.theory_base_name)
            else "File " + quote(name.path.file_name)
          val content = output_document(title, pide_document(snapshot))
          Preview(title, content)
      }
    }
  }


  /* PIDE document */

  private val document_elements =
    Rendering.foreground_elements ++ Rendering.text_color_elements ++ Rendering.markdown_elements +
    Markup.NUMERAL + Markup.COMMENT + Markup.LANGUAGE

  private val div_elements =
    Set(HTML.div.name, HTML.pre.name, HTML.par.name, HTML.list.name, HTML.enum.name,
      HTML.descr.name)

  private def html_div(html: XML.Body): Boolean =
    html exists {
      case XML.Elem(markup, body) => div_elements.contains(markup.name) || html_div(body)
      case XML.Text(_) => false
    }

  private def html_class(c: String, html: XML.Body): XML.Tree =
    if (html.forall(_ == HTML.no_text)) HTML.no_text
    else if (html_div(html)) HTML.div(c, html)
    else HTML.span(c, html)

  private def make_html(xml: XML.Body): XML.Body =
    xml map {
      case XML.Elem(Markup(Markup.LANGUAGE, Markup.Name(Markup.Language.DOCUMENT)), body) =>
        html_class(Markup.Language.DOCUMENT, make_html(body))
      case XML.Elem(Markup(Markup.MARKDOWN_PARAGRAPH, _), body) => HTML.par(make_html(body))
      case XML.Elem(Markup(Markup.MARKDOWN_ITEM, _), body) => HTML.item(make_html(body))
      case XML.Elem(Markup(Markup.Markdown_Bullet.name, _), _) => HTML.no_text
      case XML.Elem(Markup.Markdown_List(kind), body) =>
        if (kind == Markup.ENUMERATE) HTML.enum(make_html(body)) else HTML.list(make_html(body))
      case XML.Elem(markup, body) =>
        val name = markup.name
        val html =
          markup.properties match {
            case Markup.Kind(kind) if kind == Markup.COMMAND || kind == Markup.KEYWORD =>
              List(html_class(kind, make_html(body)))
            case _ =>
              make_html(body)
          }
        Rendering.foreground.get(name) orElse Rendering.text_color.get(name) match {
          case Some(c) => html_class(c.toString, html)
          case None => html_class(name, html)
        }
      case XML.Text(text) =>
        XML.Text(Symbol.decode(text))
    }

  def pide_document(snapshot: Document.Snapshot): XML.Body =
    make_html(snapshot.markup_to_XML(Text.Range.full, document_elements))



  /** build document **/

  val document_format = "pdf"

  val default_document_name = "document"
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
    document_dir: Option[Path] = None,
    tags: List[String] = Nil)
  {
    val document_target = Path.parent + Path.explode(document_name).ext(document_format)

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
        Library.trim_line(result.err),
        cat_lines(Latex.latex_errors(dir, root_name) ::: Bibtex.bibtex_errors(dir, root_name)),
        "Failed to build document in " + File.path(dir.absolute_file))
    }

    bash("if [ -f " + root_bash(document_format) + " ]; then cp -f " +
      root_bash(document_format) + " " + File.bash_path(document_target) + "; fi").check
  }


  /* Isabelle tool wrapper */

  val isabelle_tool =
    Isabelle_Tool("document", "prepare theory session document", args =>
  {
    var document_dir: Option[Path] = None
    var document_name = default_document_name
    var tags: List[String] = Nil

    val getopts = Getopts("""
Usage: isabelle document [OPTIONS]

  Options are:
    -d DIR       document output directory (default """ +
      default_document_dir(default_document_name) + """)
    -n NAME      document name (default """ + quote(default_document_name) + """)
    -t TAGS      markup for tagged regions

  Prepare the theory session document in document directory, producing the
  specified output format.
""",
      "d:" -> (arg => document_dir = Some(Path.explode(arg))),
      "n:" -> (arg => document_name = arg),
      "t:" -> (arg => tags = space_explode(',', arg)))

    val more_args = getopts(args)
    if (more_args.nonEmpty) getopts.usage()

    try {
      build_document(document_dir = document_dir, document_name = document_name, tags = tags)
    }
    catch { case ERROR(msg) => Output.writeln(msg); sys.exit(2) }
  })
}
