/*  Title:      Pure/Thy/present.scala
    Author:     Makarius

Theory presentation: HTML and LaTeX documents.
*/

package isabelle


import scala.collection.immutable.SortedMap


object Presentation
{
  /* document info */

  abstract class Document_Name
  {
    def name: String
    def path: Path = Path.basic(name)

    override def toString: String = name
  }

  object Document_Variant
  {
    def parse(name: String, tags: String): Document_Variant =
      Document_Variant(name, Library.space_explode(',', tags))

    def parse(opt: String): Document_Variant =
      Library.space_explode('=', opt) match {
        case List(name) => Document_Variant(name, Nil)
        case List(name, tags) => parse(name, tags)
        case _ => error("Malformed document variant: " + quote(opt))
      }
  }

  sealed case class Document_Variant(name: String, tags: List[String]) extends Document_Name
  {
    def print_tags: String = tags.mkString(",")
    def print: String = if (tags.isEmpty) name else name + "=" + print_tags

    def latex_sty: String =
      Library.terminate_lines(
        tags.map(tag =>
          tag.toList match {
            case '/' :: cs => "\\isafoldtag{" + cs.mkString + "}"
            case '-' :: cs => "\\isadroptag{" + cs.mkString + "}"
            case '+' :: cs => "\\isakeeptag{" + cs.mkString + "}"
            case cs => "\\isakeeptag{" + cs.mkString + "}"
          }))
  }

  sealed case class Document_Input(name: String, sources: SHA1.Digest)
    extends Document_Name

  sealed case class Document_Output(name: String, sources: SHA1.Digest, log_xz: Bytes, pdf: Bytes)
    extends Document_Name
  {
    def log: String = log_xz.uncompress().text
    def log_lines: List[String] = split_lines(log)

    def write(db: SQL.Database, session_name: String) =
      write_document(db, session_name, this)
  }


  /* SQL data model */

  object Data
  {
    val session_name = SQL.Column.string("session_name").make_primary_key
    val name = SQL.Column.string("name").make_primary_key
    val sources = SQL.Column.string("sources")
    val log_xz = SQL.Column.bytes("log_xz")
    val pdf = SQL.Column.bytes("pdf")

    val table = SQL.Table("isabelle_documents", List(session_name, name, sources, log_xz, pdf))

    def where_equal(session_name: String, name: String = ""): SQL.Source =
      "WHERE " + Data.session_name.equal(session_name) +
        (if (name == "") "" else " AND " + Data.name.equal(name))
  }

  def read_documents(db: SQL.Database, session_name: String): List[Document_Input] =
  {
    val select = Data.table.select(List(Data.name, Data.sources), Data.where_equal(session_name))
    db.using_statement(select)(stmt =>
      stmt.execute_query().iterator(res =>
      {
        val name = res.string(Data.name)
        val sources = res.string(Data.sources)
        Document_Input(name, SHA1.fake(sources))
      }).toList)
  }

  def read_document(db: SQL.Database, session_name: String, name: String): Option[Document_Output] =
  {
    val select = Data.table.select(sql = Data.where_equal(session_name, name))
    db.using_statement(select)(stmt =>
    {
      val res = stmt.execute_query()
      if (res.next()) {
        val name = res.string(Data.name)
        val sources = res.string(Data.sources)
        val log_xz = res.bytes(Data.log_xz)
        val pdf = res.bytes(Data.pdf)
        Some(Document_Output(name, SHA1.fake(sources), log_xz, pdf))
      }
      else None
    })
  }

  def write_document(db: SQL.Database, session_name: String, doc: Document_Output)
  {
    db.using_statement(Data.table.insert())(stmt =>
    {
      stmt.string(1) = session_name
      stmt.string(2) = doc.name
      stmt.string(3) = doc.sources.toString
      stmt.bytes(4) = doc.log_xz
      stmt.bytes(5) = doc.pdf
      stmt.execute()
    })
  }


  /* presentation context */

  object Context
  {
    val none: Context = new Context { def enabled: Boolean = false }
    val standard: Context = new Context { def enabled: Boolean = true }

    def dir(path: Path): Context =
      new Context {
        def enabled: Boolean = true
        override def dir(store: Sessions.Store): Path = path
      }

    def make(s: String): Context =
      if (s == ":") standard else dir(Path.explode(s))
  }

  abstract class Context private
  {
    def enabled: Boolean
    def enabled(info: Sessions.Info): Boolean = enabled || info.browser_info
    def dir(store: Sessions.Store): Path = store.presentation_dir
    def dir(store: Sessions.Store, info: Sessions.Info): Path =
      dir(store) + Path.explode(info.chapter_session)
  }


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

  def token_markups(keywords: Keyword.Keywords, tok: Token): List[String] = {
    if (keywords.is_command(tok, Keyword.theory_end))
      List(Markup.KEYWORD2, Markup.KEYWORD)
    else if (keywords.is_command(tok, Keyword.proof_asm))
      List(Markup.KEYWORD3, Markup.COMMAND)
    else if (keywords.is_command(tok, Keyword.improper))
      List(Markup.KEYWORD1, Markup.IMPROPER, Markup.COMMAND)
    else if (tok.is_command) List(Markup.KEYWORD1, Markup.COMMAND)
    else if (tok.is_delimiter) List(Markup.DELIMITER, Markup.KEYWORD)
    else if (tok.is_keyword) List(Markup.KEYWORD2, Markup.KEYWORD)
    else if (tok.is_comment) List(Markup.COMMENT)
    else {
      tok.kind match {
        case Token.Kind.VAR => List(Markup.VAR)
        case Token.Kind.TYPE_IDENT => List(Markup.TFREE)
        case Token.Kind.TYPE_VAR => List(Markup.TVAR)
        case Token.Kind.STRING => List(Markup.STRING)
        case Token.Kind.ALT_STRING => List(Markup.ALT_STRING)
        case Token.Kind.VERBATIM => List(Markup.VERBATIM)
        case Token.Kind.CARTOUCHE => List(Markup.CARTOUCHE)
        case _ => Nil
      }
    }
  }

  def session_html(
    session: String,
    deps: Sessions.Deps,
    db_context: Sessions.Database_Context,
    presentation: Context)
  {
    val info = deps.sessions_structure(session)
    val options = info.options
    val base = deps(session)

    val session_dir = presentation.dir(db_context.store, info)
    val session_fonts = Isabelle_System.make_directory(session_dir + Path.explode("fonts"))
    for (entry <- Isabelle_Fonts.fonts(hidden = true))
      File.copy(entry.path, session_fonts)

    Bytes.write(session_dir + session_graph_path,
      graphview.Graph_File.make_pdf(options, base.session_graph_display))

    val documents =
      for {
        doc <- info.document_variants
        document <- db_context.input_database(session)(read_document(_, _, doc.name))
      } yield { Bytes.write(session_dir + doc.path.pdf, document.pdf); doc }

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
        documents.map(doc => HTML.link(doc.path.pdf, HTML.text(doc.name)))

      Library.separate(HTML.break ::: HTML.nl,
        (deps_link :: readme_links ::: document_links).
          map(link => HTML.text("View ") ::: List(link))).flatten
    }

    def theory_link(name1: Document.Node.Name, body: XML.Body): XML.Tree =
    {
      val session1 = base.theory_qualifier(name1)
      val info1 = deps.sessions_structure(session1)
      val prefix =
        if (session == session1) ""
        else if (info.chapter == info1.chapter) "../" + session1 + "/"
        else "../../" + info1.chapter_session + "/"
      HTML.link(prefix + html_name(name1), body)
    }

    val theories =
      for (name <- base.session_theories)
      yield {
        val syntax = base.theory_syntax(name)
        val keywords = syntax.keywords
        val spans = syntax.parse_spans(Symbol.decode(File.read(name.path)))

        val thy_body =
        {
          val imports_offset = base.known_theories(name.theory).header.imports_offset
          var token_offset = 1
          spans.flatMap(span =>
          {
            val is_init = span.is_kind(keywords, Keyword.theory_begin, false)
            span.content.flatMap(tok =>
            {
              val text = HTML.text(tok.source)
              val item =
                if (is_init && imports_offset.isDefinedAt(token_offset)) {
                  List(theory_link(imports_offset(token_offset), text))
                }
                else text

              token_offset += tok.symbol_length

              (token_markups(keywords, tok) :\ item)(
                { case (c, body) => List(HTML.span(c, body)) })
            })
          })
        }

        val title = "Theory " + name.theory_base_name
        HTML.write_document(session_dir, html_name(name),
          List(HTML.title(title)),
          HTML.div("head", List(HTML.chapter(title))) :: List(HTML.pre("source", thy_body)))

        List(HTML.link(html_name(name), HTML.text(name.theory_base_name)))
      }

    val title = "Session " + session
    HTML.write_document(session_dir, "index.html",
      List(HTML.title(title + " (" + Distribution.version + ")")),
      HTML.div("head", List(HTML.chapter(title), HTML.par(links))) ::
       (if (theories.isEmpty) Nil
        else List(HTML.div("theories", List(HTML.section("Theories"), HTML.itemize(theories))))))
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
    make_html(snapshot.xml_markup(elements = document_elements))



  /** build documents **/

  val session_tex_path = Path.explode("session.tex")

  def tex_name(name: Document.Node.Name): String = name.theory_base_name + ".tex"
  def document_tex_name(name: Document.Node.Name): String = "document/" + tex_name(name)

  def build_documents(
    session: String,
    deps: Sessions.Deps,
    db_context: Sessions.Database_Context,
    progress: Progress = new Progress,
    output_sources: Option[Path] = None,
    output_pdf: Option[Path] = None,
    verbose: Boolean = false,
    verbose_latex: Boolean = false): List[Document_Output] =
  {
    /* session info */

    val info = deps.sessions_structure(session)
    val hierarchy = deps.sessions_structure.hierarchy(session)
    val options = info.options
    val base = deps(session)
    val graph_pdf = graphview.Graph_File.make_pdf(options, base.session_graph_display)


    /* prepare document directory */

    lazy val tex_files =
      for (name <- base.session_theories ::: base.document_theories)
      yield {
        val entry = db_context.get_export(hierarchy, name.theory, document_tex_name(name))
        Path.basic(tex_name(name)) -> entry.uncompressed
      }

    def prepare_dir1(dir: Path, doc: Document_Variant): (Path, String) =
    {
      val doc_dir = dir + Path.basic(doc.name)
      Isabelle_System.make_directory(doc_dir)

      Isabelle_System.bash("isabelle latex -o sty", cwd = doc_dir.file).check
      File.write(doc_dir + Path.explode("isabelletags.sty"), doc.latex_sty)
      for ((base_dir, src) <- info.document_files) File.copy_base(info.dir + base_dir, src, doc_dir)

      File.write(doc_dir + session_tex_path,
        Library.terminate_lines(
          base.session_theories.map(name => "\\input{" + tex_name(name) + "}")))

      for ((path, tex) <- tex_files) Bytes.write(doc_dir + path, tex)

      val root1 = "root_" + doc.name
      val root = if ((doc_dir + Path.explode(root1).tex).is_file) root1 else "root"

      (doc_dir, root)
    }

    def prepare_dir2(dir: Path, doc: Document_Variant): Unit =
    {
      val doc_dir = dir + Path.basic(doc.name)

      // non-deterministic, but irrelevant
      Bytes.write(doc_dir + session_graph_path, graph_pdf)
    }


    /* produce documents */

    val documents =
      for (doc <- info.documents)
      yield {
        Isabelle_System.with_tmp_dir("document")(tmp_dir =>
        {
          progress.echo("Preparing " + session + "/" + doc.name + " ...")
          val start = Time.now()


          // prepare sources

          val (doc_dir, root) = prepare_dir1(tmp_dir, doc)
          val digests = File.find_files(doc_dir.file, follow_links = true).map(SHA1.digest)
          val sources = SHA1.digest_set(digests)
          prepare_dir2(tmp_dir, doc)

          for (dir <- output_sources) {
            prepare_dir1(dir, doc)
            prepare_dir2(dir, doc)
          }


          // old document from database

          val old_document =
            for {
              old_doc <- db_context.input_database(session)(read_document(_, _, doc.name))
              if old_doc.sources == sources
            }
            yield {
              Bytes.write(doc_dir + doc.path.pdf, old_doc.pdf)
              old_doc
            }

          old_document getOrElse {
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
                bash("./build pdf " + Bash.string(doc.name))
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
                "Failed to build document " + quote(doc.name))
            }
            else if (!result_path.is_file) {
              error("Bad document result: expected to find " + root_pdf)
            }
            else {
              val stop = Time.now()
              val timing = stop - start
              progress.echo("Finished " + session + "/" + doc.name +
                " (" + timing.message_hms + " elapsed time)")

              val log_xz = Bytes(cat_lines(result.out_lines ::: result.err_lines)).compress()
              val pdf = Bytes.read(result_path)
              Document_Output(doc.name, sources, log_xz, pdf)
            }
          }
        })
      }

    for (dir <- output_pdf; doc <- documents) {
      Isabelle_System.make_directory(dir)
      val path = dir + doc.path.pdf
      Bytes.write(path, doc.pdf)
      progress.echo("Document at " + path.absolute)
    }

    documents
  }


  /* Isabelle tool wrapper */

  val isabelle_tool =
    Isabelle_Tool("document", "prepare session theory document", Scala_Project.here, args =>
    {
      var output_sources: Option[Path] = None
      var output_pdf: Option[Path] = None
      var verbose_latex = false
      var dirs: List[Path] = Nil
      var options = Options.init()
      var verbose_build = false

      val getopts = Getopts(
        """
Usage: isabelle document [OPTIONS] SESSION

  Options are:
    -O DIR       output directory for LaTeX sources and resulting PDF
    -P DIR       output directory for resulting PDF
    -S DIR       output directory for LaTeX sources
    -V           verbose latex
    -d DIR       include session directory
    -o OPTION    override Isabelle system OPTION (via NAME=VAL or NAME)
    -v           verbose build

  Prepare the theory document of a session.
""",
        "O:" -> (arg =>
          {
            val dir = Path.explode(arg)
            output_sources = Some(dir)
            output_pdf = Some(dir)
          }),
        "P:" -> (arg => { output_pdf = Some(Path.explode(arg)) }),
        "S:" -> (arg => { output_sources = Some(Path.explode(arg)) }),
        "V" -> (_ => verbose_latex = true),
        "d:" -> (arg => dirs = dirs ::: List(Path.explode(arg))),
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
        val res =
          Build.build(options, selection = Sessions.Selection.session(session),
            dirs = dirs, progress = progress, verbose = verbose_build)
        if (!res.ok) error("Failed to build session " + quote(session))

        val deps =
          Sessions.load_structure(options + "document=pdf", dirs = dirs).
            selection_deps(Sessions.Selection.session(session))

        if (output_sources.isEmpty && output_pdf.isEmpty) {
          progress.echo_warning("No output directory")
        }

        using(store.open_database_context())(db_context =>
          build_documents(session, deps, db_context, progress = progress,
            output_sources = output_sources, output_pdf = output_pdf,
            verbose = true, verbose_latex = verbose_latex))
      }
    })
}
