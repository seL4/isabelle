/*  Title:      Pure/Thy/present.scala
    Author:     Makarius

Theory presentation: HTML and LaTeX documents.
*/

package isabelle


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


  /* present session */

  val session_graph_path = Path.explode("session_graph.pdf")
  val readme_path = Path.basic("README.html")

  def html_name(name: Document.Node.Name): String = name.theory_base_name + ".html"
  def document_html_name(name: Document.Node.Name): String = "document/" + html_name(name)

  def theory_link(name: Document.Node.Name): XML.Tree =
    HTML.link(html_name(name), HTML.text(name.theory_base_name))

  def session_html(session: String, deps: Sessions.Deps, store: Sessions.Store): Path =
  {
    val info = deps.sessions_structure(session)
    val options = info.options
    val base = deps(session)

    val session_dir = store.browser_info + info.chapter_session
    val session_fonts = Isabelle_System.make_directory(session_dir + Path.explode("fonts"))
    for (entry <- Isabelle_Fonts.fonts(hidden = true))
      File.copy(entry.path, session_fonts)

    Bytes.write(session_dir + session_graph_path,
      graphview.Graph_File.make_pdf(options, base.session_graph_display))

    val links =
    {
      val deps_link =
        HTML.link(session_graph_path, HTML.text("theory dependencies"))

      val readme_links =
        if ((info.dir + readme_path).is_file) {
          File.copy(info.dir + readme_path, session_dir + readme_path)
          List(HTML.link(readme_path, HTML.text("README")))
        }
        else Nil

      val document_links =
        for ((name, _) <- info.documents)
          yield HTML.link(Path.basic(name).pdf, HTML.text(name))

      Library.separate(HTML.break ::: HTML.nl,
        (deps_link :: readme_links ::: document_links).
          map(link => HTML.text("View ") ::: List(link))).flatten
    }

    val theories =
      using(store.open_database(session))(db =>
        for {
          name <- base.session_theories
          entry <- Export.read_entry(db, session, name.theory, document_html_name(name))
        } yield name -> entry.uncompressed(cache = store.xz_cache))

    val theories_body =
      HTML.itemize(for ((name, _) <- theories) yield List(theory_link(name)))

    val title = "Session " + session
    HTML.write_document(session_dir, "index.html",
      List(HTML.title(title + " (" + Distribution.version + ")")),
      HTML.div("head", List(HTML.chapter(title), HTML.par(links))) ::
       (if (theories.isEmpty) Nil
        else List(HTML.div("theories", List(HTML.section("Theories"), theories_body)))))

    for ((name, html) <- theories) Bytes.write(session_dir + Path.basic(html_name(name)), html)

    session_dir
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



  /** build documents **/

  val session_tex_path = Path.explode("session.tex")

  def tex_name(name: Document.Node.Name): String = name.theory_base_name + ".tex"
  def document_tex_name(name: Document.Node.Name): String = "document/" + tex_name(name)

  def isabelletags(tags: List[String]): String =
    Library.terminate_lines(
      tags.map(tag =>
        tag.toList match {
          case '/' :: cs => "\\isafoldtag{" + cs.mkString + "}"
          case '-' :: cs => "\\isadroptag{" + cs.mkString + "}"
          case '+' :: cs => "\\isakeeptag{" + cs.mkString + "}"
          case cs => "\\isakeeptag{" + cs.mkString + "}"
        }))

  def build_documents(
    session: String,
    deps: Sessions.Deps,
    store: Sessions.Store,
    progress: Progress = new Progress,
    verbose: Boolean = false,
    verbose_latex: Boolean = false): List[(String, Bytes)] =
  {
    /* session info */

    val info = deps.sessions_structure(session)
    val options = info.options
    val base = deps(session)
    val graph_pdf = graphview.Graph_File.make_pdf(options, base.session_graph_display)

    def find_tex(name: Document.Node.Name): Option[Bytes] =
      deps.sessions_structure.build_requirements(List(session)).reverse.view
        .map(session_name =>
          using(store.open_database(session_name))(db =>
            Export.read_entry(db, session_name, name.theory, document_tex_name(name)).
              map(_.uncompressed(cache = store.xz_cache))))
        .collectFirst({ case Some(x) => x })


    /* prepare document directory */

    lazy val tex_files =
      for (name <- base.session_theories ::: base.document_theories)
        yield Path.basic(tex_name(name)) -> find_tex(name).getOrElse(Bytes.empty)

    def prepare_dir(dir: Path, doc_name: String, doc_tags: List[String]): (Path, String) =
    {
      val doc_dir = dir + Path.basic(doc_name)
      Isabelle_System.make_directory(doc_dir)

      Isabelle_System.bash("isabelle latex -o sty", cwd = doc_dir.file).check
      File.write(doc_dir + Path.explode("isabelletags.sty"), isabelletags(doc_tags))
      for ((base_dir, src) <- info.document_files) File.copy_base(info.dir + base_dir, src, doc_dir)
      Bytes.write(doc_dir + session_graph_path, graph_pdf)

      File.write(doc_dir + session_tex_path,
        Library.terminate_lines(
          base.session_theories.map(name => "\\input{" + tex_name(name) + "}")))

      for ((path, tex) <- tex_files) Bytes.write(doc_dir + path, tex)

      val root1 = "root_" + doc_name
      val root = if ((doc_dir + Path.explode(root1).tex).is_file) root1 else "root"

      (doc_dir, root)
    }


    /* produce documents */

    val doc_output = info.document_output

    val docs =
      for ((doc_name, doc_tags) <- info.documents)
      yield {
        Isabelle_System.with_tmp_dir("document")(tmp_dir =>
        {
          val (doc_dir, root) = prepare_dir(tmp_dir, doc_name, doc_tags)
          doc_output.foreach(prepare_dir(_, doc_name, doc_tags))


          // bash scripts

          def root_bash(ext: String): String = Bash.string(root + "." + ext)

          def latex_bash(fmt: String = "pdf", ext: String = "tex"): String =
            "isabelle latex -o " + Bash.string(fmt) + " " + Bash.string(root + "." + ext)

          def bash(items: String*): Process_Result =
            progress.bash(items.mkString(" && "), cwd = doc_dir.file,
              echo = verbose_latex, watchdog = Time.seconds(0.5))


          // prepare document

          val result =
            if ((doc_dir + Path.explode("build")).is_file) {
              bash("./build pdf " + Bash.string(doc_name))
            }
            else {
              bash(
                latex_bash(),
                "{ [ ! -f " + root_bash("bib") + " ] || " + latex_bash("bbl") + "; }",
                "{ [ ! -f " + root_bash("idx") + " ] || " + latex_bash("idx") + "; }",
                latex_bash(),
                latex_bash())
            }


          // result

          val root_pdf = Path.basic(root).pdf
          val result_path = doc_dir + root_pdf

          if (!result.ok) {
            cat_error(
              Library.trim_line(result.err),
              cat_lines(Latex.latex_errors(doc_dir, root) ::: Bibtex.bibtex_errors(doc_dir, root)),
              "Failed to build document " + quote(doc_name))
          }
          else if (!result_path.is_file) {
            error("Bad document result: expected to find " + root_pdf)
          }
          else doc_name -> Bytes.read(result_path)
        })
      }

    def output(dir: Path)
    {
      Isabelle_System.make_directory(dir)
      for ((name, pdf) <- docs) {
        val path = dir + Path.basic(name).pdf
        Bytes.write(path, pdf)
        progress.echo_document(path)
      }
    }

    if (info.options.bool("browser_info") || doc_output.isEmpty) {
      output(store.browser_info + info.chapter_session)
    }

    doc_output.foreach(output)

    docs
  }


  /* Isabelle tool wrapper */

  val isabelle_tool =
    Isabelle_Tool("document", "prepare session theory document", args =>
    {
      var verbose_latex = false
      var dirs: List[Path] = Nil
      var no_build = false
      var options = Options.init()
      var verbose_build = false

      val getopts = Getopts(
        """
Usage: isabelle document [OPTIONS] SESSION

  Options are:
    -O           set option "document_output", relative to current directory
    -V           verbose latex
    -d DIR       include session directory
    -n           no build of session
    -o OPTION    override Isabelle system OPTION (via NAME=VAL or NAME)
    -v           verbose build

  Prepare the theory document of a session.
""",
        "O:" -> (arg => options += ("document_output=" + Path.explode(arg).absolute.implode)),
        "V" -> (_ => verbose_latex = true),
        "d:" -> (arg => dirs = dirs ::: List(Path.explode(arg))),
        "n" -> (_ => no_build = true),
        "o:" -> (arg => options = options + arg),
        "v" -> (_ => verbose_build = true))

      val more_args = getopts(args)
      val session =
        more_args match {
          case List(a) => a
          case _ => getopts.usage()
        }

      val progress = new Console_Progress(verbose = verbose_build)
      val store = Sessions.store(options)

      progress.interrupt_handler {
        if (!no_build) {
          val res =
            Build.build(options, selection = Sessions.Selection.session(session),
              dirs = dirs, progress = progress, verbose = verbose_build)
          if (!res.ok) error("Failed to build session " + quote(session))
        }

        val deps =
          Sessions.load_structure(options + "document=pdf", dirs = dirs).
            selection_deps(Sessions.Selection.session(session))

        build_documents(session, deps, store, progress = progress,
          verbose = true, verbose_latex = verbose_latex)
      }
    })
}
