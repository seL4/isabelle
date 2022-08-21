/*  Title:      Pure/Thy/browser_info.scala
    Author:     Makarius

HTML presentation of PIDE document information.
*/

package isabelle


import scala.annotation.tailrec
import scala.collection.immutable.SortedMap
import scala.collection.mutable


object Browser_Info {
  /** HTML documents **/

  /* HTML context */

  def html_context(
    sessions_structure: Sessions.Structure,
    elements: Elements,
    root_dir: Path = Path.current,
    document_info: Document_Info = Document_Info.empty
  ): HTML_Context = new HTML_Context(sessions_structure, elements, root_dir, document_info)

  class HTML_Context private[Browser_Info](
    sessions_structure: Sessions.Structure,
    val elements: Elements,
    val root_dir: Path,
    val document_info: Document_Info
  ) {
    /* directory structure and resources */

    def theory_by_name(session: String, theory: String): Option[Document_Info.Theory] =
      document_info.theory_by_name(session, theory)

    def theory_by_file(session: String, file: String): Option[Document_Info.Theory] =
      document_info.theory_by_file(session, file)

    def session_dir(session: String): Path =
      root_dir + Path.explode(sessions_structure(session).chapter_session)

    def theory_html(theory: Document_Info.Theory): Path =
    {
      def check(name: String): Option[Path] = {
        val path = Path.explode(name).html
        if (Path.eq_case_insensitive(path, Path.index_html)) None
        else Some(path)
      }
      check(theory.print_short) orElse check(theory.name) getOrElse
        error("Illegal global theory name " + quote(theory.name) +
          " (conflict with " + Path.index_html + ")")
    }

    def file_html(file: String): Path =
      Path.explode(file).squash.html

    def smart_html(theory: Document_Info.Theory, file: String): Path =
      if (File.is_thy(file)) theory_html(theory) else file_html(file)


    /* HTML content */

    def head(title: String, rest: XML.Body = Nil): XML.Tree =
      HTML.div("head", HTML.chapter(title) :: rest)

    def source(body: XML.Body): XML.Tree = HTML.pre("source", body)

    def contents(
      heading: String,
      items: List[XML.Body],
      css_class: String = "contents"
    ) : List[XML.Elem] = {
      if (items.isEmpty) Nil
      else List(HTML.div(css_class, List(HTML.section(heading), HTML.itemize(items))))
    }

    val isabelle_css: String = File.read(HTML.isabelle_css)

    def html_document(title: String, body: XML.Body, fonts_css: String): HTML_Document = {
      val content =
        HTML.output_document(
          List(
            HTML.style(fonts_css + "\n\n" + isabelle_css),
            HTML.title(title)),
          List(HTML.source(body)), css = "", structural = false)
      HTML_Document(title, content)
    }
  }

  sealed case class HTML_Document(title: String, content: String)


  /* presentation elements */

  sealed case class Elements(
    html: Markup.Elements = Markup.Elements.empty,
    entity: Markup.Elements = Markup.Elements.empty,
    language: Markup.Elements = Markup.Elements.empty)

  val elements1: Elements =
    Elements(
      html = Rendering.foreground_elements ++ Rendering.text_color_elements +
        Markup.NUMERAL + Markup.COMMENT + Markup.ENTITY + Markup.LANGUAGE,
      entity = Markup.Elements(Markup.THEORY, Markup.TYPE_NAME, Markup.CONSTANT, Markup.FACT,
        Markup.CLASS, Markup.LOCALE, Markup.FREE))

  val elements2: Elements =
    Elements(
      html = elements1.html ++ Rendering.markdown_elements,
      language = Markup.Elements(Markup.Language.DOCUMENT))


  /* formal entities */

  object Theory_Ref {
    def unapply(props: Properties.T): Option[String] =
      (props, props) match {
        case (Markup.Kind(Markup.THEORY), Markup.Name(theory)) => Some(theory)
        case _ => None
      }
  }

  object Entity_Ref {
    def unapply(props: Properties.T): Option[(String, String, String)] =
      (props, props, props, props) match {
        case (Markup.Entity.Ref.Prop(_), Position.Def_File(file), Markup.Kind(kind), Markup.Name(name))
        if Path.is_wellformed(file) => Some((file, kind, name))
        case _ => None
      }
  }

  object Node_Context {
    val empty: Node_Context = new Node_Context

    def make(
      html_context: HTML_Context,
      session_name: String,
      theory_name: String,
      file_name: String,
      node_dir: Path,
    ): Node_Context =
      new Node_Context {
        private val session_dir = html_context.session_dir(session_name)

        private val seen_ranges: mutable.Set[Symbol.Range] = mutable.Set.empty

        override def make_def(range: Symbol.Range, body: XML.Body): Option[XML.Elem] =
          body match {
            case List(XML.Elem(Markup("span", List("id" -> _)), _)) => None
            case _ =>
              for (theory <- html_context.theory_by_name(session_name, theory_name))
              yield {
                val body1 =
                  if (seen_ranges.contains(range)) {
                    HTML.entity_def(HTML.span(HTML.id(offset_id(range)), body))
                  }
                  else HTML.span(body)
                theory.get_defs(file_name, range).foldLeft(body1) {
                  case (elem, entity) =>
                    HTML.entity_def(HTML.span(HTML.id(entity.kname), List(elem)))
                }
              }
          }

        private def offset_id(range: Text.Range): String =
          "offset_" + range.start + ".." + range.stop

        override def make_ref(props: Properties.T, body: XML.Body): Option[XML.Elem] = {
          props match {
            case Theory_Ref(thy_name) =>
              for (theory <- html_context.theory_by_name(session_name, thy_name))
              yield {
                val html_path = session_dir + html_context.theory_html(theory)
                val html_link = HTML.relative_href(html_path, base = Some(node_dir))
                HTML.link(html_link, body)
              }
            case Entity_Ref(def_file, kind, name) =>
              def logical_ref(theory: Document_Info.Theory): Option[String] =
                theory.get_def(def_file, kind, name).map(_.kname)

              def physical_ref(theory: Document_Info.Theory): Option[String] =
                props match {
                  case Position.Def_Range(range) if theory.name == theory_name =>
                    seen_ranges += range
                    Some(offset_id(range))
                  case _ => None
                }

              for {
                theory <- html_context.theory_by_file(session_name, def_file)
                html_ref <- logical_ref(theory) orElse physical_ref(theory)
              }
              yield {
                val html_path = session_dir + html_context.smart_html(theory, def_file)
                val html_link = HTML.relative_href(html_path, base = Some(node_dir))
                HTML.entity_ref(HTML.link(html_link + "#" + html_ref, body))
              }
            case _ => None
          }
        }
      }
  }

  class Node_Context {
    def make_def(range: Symbol.Range, body: XML.Body): Option[XML.Elem] = None
    def make_ref(props: Properties.T, body: XML.Body): Option[XML.Elem] = None

    val div_elements: Set[String] =
      Set(HTML.div.name, HTML.pre.name, HTML.par.name, HTML.list.name, HTML.`enum`.name,
        HTML.descr.name)

    def make_html(elements: Elements, xml: XML.Body): XML.Body = {
      def html_div(html: XML.Body): Boolean =
        html exists {
          case XML.Elem(markup, body) => div_elements.contains(markup.name) || html_div(body)
          case XML.Text(_) => false
        }

      def html_class(c: String, html: XML.Body): XML.Body =
        if (c == "") html
        else if (html_div(html)) List(HTML.div(c, html))
        else List(HTML.span(c, html))

      def html_body(xml_body: XML.Body, end_offset: Symbol.Offset): (XML.Body, Symbol.Offset) =
        xml_body.foldRight((List.empty[XML.Tree], end_offset)) { case (tree, (res, end_offset1)) =>
          val (res1, offset) = html_body_single(tree, end_offset1)
          (res1 ++ res, offset)
        }

      @tailrec
      def html_body_single(xml_tree: XML.Tree, end_offset: Symbol.Offset): (XML.Body, Symbol.Offset) =
        xml_tree match {
          case XML.Wrapped_Elem(markup, _, body) => html_body_single(XML.Elem(markup, body), end_offset)
          case XML.Elem(Markup(Markup.ENTITY, props @ Markup.Kind(kind)), body) =>
            val (body1, offset) = html_body(body, end_offset)
            if (elements.entity(kind)) {
              make_ref(props, body1) match {
                case Some(link) => (List(link), offset)
                case None => (body1, offset)
              }
            }
            else (body1, offset)
          case XML.Elem(Markup(Markup.LANGUAGE, Markup.Name(name)), body) =>
            val (body1, offset) = html_body(body, end_offset)
            (html_class(if (elements.language(name)) name else "", body1), offset)
          case XML.Elem(Markup(Markup.MARKDOWN_PARAGRAPH, _), body) =>
            val (body1, offset) = html_body(body, end_offset)
            (List(HTML.par(body1)), offset)
          case XML.Elem(Markup(Markup.MARKDOWN_ITEM, _), body) =>
            val (body1, offset) = html_body(body, end_offset)
            (List(HTML.item(body1)), offset)
          case XML.Elem(Markup(Markup.Markdown_Bullet.name, _), text) =>
            (Nil, end_offset - XML.symbol_length(text))
          case XML.Elem(Markup.Markdown_List(kind), body) =>
            val (body1, offset) = html_body(body, end_offset)
            if (kind == Markup.ENUMERATE) (List(HTML.`enum`(body1)), offset)
            else (List(HTML.list(body1)), offset)
          case XML.Elem(markup, body) =>
            val name = markup.name
            val (body1, offset) = html_body(body, end_offset)
            val html =
              markup.properties match {
                case Markup.Kind(kind) if kind == Markup.COMMAND || kind == Markup.KEYWORD =>
                  html_class(kind, body1)
                case _ =>
                  body1
              }
            Rendering.foreground.get(name) orElse Rendering.text_color.get(name) match {
              case Some(c) => (html_class(c.toString, html), offset)
              case None => (html_class(name, html), offset)
            }
          case XML.Text(text) =>
            val offset = end_offset - Symbol.length(text)
            val body = HTML.text(Symbol.decode(text))
            make_def(Text.Range(offset, end_offset), body) match {
              case Some(body1) => (List(body1), offset)
              case None => (body, offset)
            }
        }

      html_body(xml, XML.symbol_length(xml) + 1)._1
    }
  }


  /* PIDE HTML document */

  def html_document(
    snapshot: Document.Snapshot,
    html_context: HTML_Context,
    plain_text: Boolean = false,
    fonts_css: String = HTML.fonts_css()
  ): HTML_Document = {
    require(!snapshot.is_outdated, "document snapshot outdated")

    val name = snapshot.node_name
    if (plain_text) {
      val title = "File " + Symbol.cartouche_decoded(name.path.file_name)
      val body = HTML.text(snapshot.node.source)
      html_context.html_document(title, body, fonts_css)
    }
    else {
      Resources.html_document(snapshot) getOrElse {
        val title =
          if (name.is_theory) "Theory " + quote(name.theory_base_name)
          else "File " + Symbol.cartouche_decoded(name.path.file_name)
        val xml = snapshot.xml_markup(elements = html_context.elements.html)
        val body = Node_Context.empty.make_html(html_context.elements, xml)
        html_context.html_document(title, body, fonts_css)
      }
    }
  }



  /** HTML presentation **/

  /* presentation context */

  object Context {
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

  abstract class Context private {
    def enabled: Boolean
    def enabled(info: Sessions.Info): Boolean = enabled || info.browser_info
    def dir(store: Sessions.Store): Path = store.presentation_dir
  }


  /* maintain chapter index */

  private val sessions_path = Path.basic(".sessions")

  private def read_sessions(dir: Path): List[(String, String)] = {
    val path = dir + sessions_path
    if (path.is_file) {
      import XML.Decode._
      list(pair(string, string))(Symbol.decode_yxml(File.read(path)))
    }
    else Nil
  }

  def update_chapter(
    presentation_dir: Path,
    chapter: String,
    new_sessions: List[(String, String)]
  ): Unit = {
    val dir = Isabelle_System.make_directory(presentation_dir + Path.basic(chapter))

    val sessions0 =
      try { read_sessions(dir) }
      catch { case _: XML.Error => Nil }

    val sessions = (SortedMap.empty[String, String] ++ sessions0 ++ new_sessions).toList
    File.write(dir + sessions_path,
      {
        import XML.Encode._
        YXML.string_of_body(list(pair(string, string))(sessions))
      })

    val title = "Isabelle/" + chapter + " sessions"
    HTML.write_document(dir, "index.html",
      List(HTML.title(title + Isabelle_System.isabelle_heading())),
      HTML.chapter(title) ::
       (if (sessions.isEmpty) Nil
        else
          List(HTML.div("sessions",
            List(HTML.description(
              sessions.map({ case (name, description) =>
                val descr = Symbol.trim_blank_lines(description)
                (List(HTML.link(name + "/index.html", HTML.text(name))),
                  if (descr == "") Nil
                  else HTML.break ::: List(HTML.pre(HTML.text(descr)))) })))))),
      root = Some(presentation_dir))
  }

  def update_root(presentation_dir: Path): Unit = {
    Isabelle_System.make_directory(presentation_dir)
    HTML.init_fonts(presentation_dir)
    Isabelle_System.copy_file(Path.explode("~~/lib/logo/isabelle.gif"),
      presentation_dir + Path.explode("isabelle.gif"))
    val title = "The " + XML.text(Isabelle_System.isabelle_name()) + " Library"
    File.write(presentation_dir + Path.explode("index.html"),
      HTML.header +
"""
<head>
  """ + HTML.head_meta + """
  <title>""" + title + """</title>
</head>

<body text="#000000" bgcolor="#FFFFFF" link="#0000FF" vlink="#000099" alink="#404040">
  <center>
    <table width="100%" border="0" cellspacing="10" cellpadding="0">
      <tr>
        <td width="20%" valign="middle" align="center"><a href="https://isabelle.in.tum.de/"><img align="bottom" src="isabelle.gif" width="100" height="86" alt="[Isabelle]" border="0" /></a></td>

        <td width="80%" valign="middle" align="center">
          <table width="90%" border="0" cellspacing="0" cellpadding="20">
            <tr>
              <td valign="middle" align="center" bgcolor="#AACCCC"><font face="Helvetica,Arial" size="+2">""" + title + """</font></td>
            </tr>
          </table>
        </td>
      </tr>
    </table>
  </center>
  <hr />
""" + File.read(Path.explode("~~/lib/html/library_index_content.template")) +
"""
</body>
""" + HTML.footer)
  }


  /* present session */

  val session_graph_path: Path = Path.explode("session_graph.pdf")

  def session_html(
    html_context: HTML_Context,
    session_context: Export.Session_Context,
    progress: Progress = new Progress,
    verbose: Boolean = false,
  ): Unit = {
    val session_name = session_context.session_name
    val session_info = session_context.sessions_structure(session_name)

    val session_dir =
      Isabelle_System.make_directory(html_context.session_dir(session_name)).expand

    progress.echo("Presenting " + session_name + " in " + session_dir + " ...")

    val session = html_context.document_info.the_session(session_name)

    Bytes.write(session_dir + session_graph_path,
      graphview.Graph_File.make_pdf(session_info.options,
        session_context.session_base.session_graph_display))

    val document_variants =
      for {
        doc <- session_info.document_variants
        db <- session_context.session_db()
        document <- Document_Build.read_document(db, session_name, doc.name)
      }
      yield {
        val doc_path = session_dir + doc.path.pdf
        if (Path.eq_case_insensitive(doc.path.pdf, session_graph_path)) {
          error("Illegal document variant " + quote(doc.name) +
            " (conflict with " + session_graph_path + ")")
        }
        if (verbose) progress.echo("Presenting document " + session_name + "/" + doc.name)
        if (session_info.document_echo) progress.echo("Document at " + doc_path)
        Bytes.write(doc_path, document.pdf)
        doc
      }

    val document_links = {
      val link1 = HTML.link(session_graph_path, HTML.text("theory dependencies"))
      val links2 = document_variants.map(doc => HTML.link(doc.path.pdf, HTML.text(doc.name)))
      Library.separate(HTML.break ::: HTML.nl,
        (link1 :: links2).map(link => HTML.text("View ") ::: List(link))).flatten
    }

    def present_theory(theory_name: String): XML.Body = {
      progress.expose_interrupt()

      def err(): Nothing =
        error("Missing document information for theory: " + quote(theory_name))

      val command = Build_Job.read_theory(session_context.theory(theory_name)) getOrElse err()
      val theory = html_context.theory_by_name(session_name, theory_name) getOrElse err()

      if (verbose) progress.echo("Presenting theory " + quote(theory_name))
      val snapshot = Document.State.init.snippet(command)

      val thy_elements = theory.elements(html_context.elements)

      def node_context(file_name: String, node_dir: Path): Node_Context =
        Node_Context.make(html_context, session_name, theory_name, file_name, node_dir)

      val thy_html =
        html_context.source(
          node_context(theory.thy_file, session_dir).
            make_html(thy_elements, snapshot.xml_markup(elements = thy_elements.html)))

      val files =
        for {
          (blob, xml) <- snapshot.xml_markup_blobs(elements = thy_elements.html)
          if xml.nonEmpty
        }
        yield {
          progress.expose_interrupt()
          val file_name = blob.name.node
          if (verbose) progress.echo("Presenting file " + quote(file_name))

          val file_html = session_dir + html_context.file_html(file_name)
          val file_dir = file_html.dir
          val html_link = HTML.relative_href(file_html, base = Some(session_dir))
          val html =
            html_context.source(
              node_context(file_name, file_dir).make_html(thy_elements, xml))

          val file_title = "File " + Symbol.cartouche_decoded(blob.src_path.implode_short)
          HTML.write_document(file_dir, file_html.file_name,
            List(HTML.title(file_title)), List(html_context.head(file_title), html),
            root = Some(html_context.root_dir))
          List(HTML.link(html_link, HTML.text(file_title)))
        }

      val thy_title = "Theory " + theory.print_short
      HTML.write_document(session_dir, html_context.theory_html(theory).implode,
        List(HTML.title(thy_title)), List(html_context.head(thy_title), thy_html),
        root = Some(html_context.root_dir))

      List(HTML.link(html_context.theory_html(theory),
        HTML.text(theory.print_short) :::
        (if (files.isEmpty) Nil else List(HTML.itemize(files)))))
    }

    val theories = session.used_theories.map(present_theory)

    val title = "Session " + session_name
      HTML.write_document(session_dir, "index.html",
        List(HTML.title(title + Isabelle_System.isabelle_heading())),
        html_context.head(title, List(HTML.par(document_links))) ::
          html_context.contents("Theories", theories),
        root = Some(html_context.root_dir))
  }
}
