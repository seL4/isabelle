/*  Title:      Pure/Thy/presentation.scala
    Author:     Makarius

HTML presentation of PIDE document content.
*/

package isabelle


import scala.annotation.tailrec
import scala.collection.immutable.SortedMap
import scala.collection.mutable


object Presentation
{
  /** HTML documents **/

  /* HTML context */

  val fonts_path = Path.explode("fonts")

  sealed case class HTML_Document(title: String, content: String)

  def html_context(fonts_url: String => String = HTML.fonts_url()): HTML_Context =
    new HTML_Context(fonts_url)

  final class HTML_Context private[Presentation](fonts_url: String => String)
  {
    def init_fonts(dir: Path): Unit =
    {
      val fonts_dir = Isabelle_System.make_directory(dir + fonts_path)
      for (entry <- Isabelle_Fonts.fonts(hidden = true))
        Isabelle_System.copy_file(entry.path, fonts_dir)
    }

    def head(title: String, rest: XML.Body = Nil): XML.Tree =
      HTML.div("head", HTML.chapter(title) :: rest)

    def source(body: XML.Body): XML.Tree = HTML.pre("source", body)

    def offset_ref(offset: Text.Range): String =
      "offset/" + offset.start + ".." + offset.stop

    def export_ref(entity: Entity): String =
      Export_Theory.export_kind(entity.kind) + "/" + entity.name

    def contents(heading: String, items: List[XML.Body], css_class: String = "contents")
      : List[XML.Elem] =
    {
      if (items.isEmpty) Nil
      else List(HTML.div(css_class, List(HTML.section(heading), HTML.itemize(items))))
    }

    def output_document(title: String, body: XML.Body): String =
      HTML.output_document(
        List(
          HTML.style(HTML.fonts_css(fonts_url) + "\n\n" + File.read(HTML.isabelle_css)),
          HTML.title(title)),
        List(HTML.source(body)), css = "", structural = false)

    def html_document(title: String, body: XML.Body): HTML_Document =
      HTML_Document(title, output_document(title, body))
  }


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

  type Entity = Export_Theory.Entity[Export_Theory.No_Content]

  case class Entity_Context(node: Document.Node.Name)
  {
    val seen_ranges: mutable.Set[Symbol.Range] = mutable.Set.empty
  }


  /* HTML output */

  private val div_elements =
    Set(HTML.div.name, HTML.pre.name, HTML.par.name, HTML.list.name, HTML.enum.name,
      HTML.descr.name)

  def make_html(
    name: Document.Node.Name,
    elements: Elements,
    entity_anchor: (Entity_Context, Symbol.Range, XML.Body) => Option[XML.Tree],
    entity_link: (Entity_Context, Properties.T, XML.Body) => Option[XML.Tree],
    xml: XML.Body): XML.Body =
  {
    val context = Entity_Context(name)

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
            entity_link(context, props, body1) match {
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
          if (kind == Markup.ENUMERATE) (List(HTML.enum(body1)), offset)
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
          entity_anchor(context, Text.Range(offset, end_offset), body) match {
            case Some(body1) => (List(body1), offset)
            case None => (body, offset)
          }
      }

    html_body(xml, XML.symbol_length(xml) + 1)._1
  }


  /* PIDE HTML document */

  def html_document(
    resources: Resources,
    snapshot: Document.Snapshot,
    html_context: HTML_Context,
    elements: Elements,
    plain_text: Boolean = false): HTML_Document =
  {
    require(!snapshot.is_outdated, "document snapshot outdated")

    val name = snapshot.node_name
    if (plain_text) {
      val title = "File " + Symbol.cartouche_decoded(name.path.file_name)
      val body = HTML.text(snapshot.node.source)
      html_context.html_document(title, body)
    }
    else {
      resources.html_document(snapshot) getOrElse {
        val title =
          if (name.is_theory) "Theory " + quote(name.theory_base_name)
          else "File " + Symbol.cartouche_decoded(name.path.file_name)
        val xml = snapshot.xml_markup(elements = elements.html)
        val body = make_html(name, elements, (_, _, _) => None, (_, _, _) => None, xml)
        html_context.html_document(title, body)
      }
    }
  }



  /** HTML presentation **/

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


  /* maintain chapter index */

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

  private def write_sessions(dir: Path, sessions: List[(String, String)]): Unit =
  {
    import XML.Encode._
    File.write(dir + sessions_path, YXML.string_of_body(list(pair(string, string))(sessions)))
  }

  def update_chapter_index(
    browser_info: Path, chapter: String, new_sessions: List[(String, String)]): Unit =
  {
    val dir = Isabelle_System.make_directory(browser_info + Path.basic(chapter))

    val sessions0 =
      try { read_sessions(dir) }
      catch { case _: XML.Error => Nil }

    val sessions = (SortedMap.empty[String, String] ++ sessions0 ++ new_sessions).toList
    write_sessions(dir, sessions)

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
                  else HTML.break ::: List(HTML.pre(HTML.text(descr)))) })))))))
  }

  def make_global_index(browser_info: Path): Unit =
  {
    if (!(browser_info + Path.explode("index.html")).is_file) {
      Isabelle_System.make_directory(browser_info)
      Isabelle_System.copy_file(Path.explode("~~/lib/logo/isabelle.gif"),
        browser_info + Path.explode("isabelle.gif"))
      val title = "The " + XML.text(Isabelle_System.isabelle_name()) + " Library"
      File.write(browser_info + Path.explode("index.html"),
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
  }


  /* cache */

  class Entity_Cache private(cache: mutable.Map[Document.Node.Name, Seq[Entity]])
  {
    def get_or_update(node: Document.Node.Name, e: => Seq[Entity]): Seq[Entity] =
      cache.getOrElseUpdate(node, e)
  }
  object Entity_Cache
  {
    def empty: Entity_Cache = new Entity_Cache(mutable.Map.empty)
  }

  /* present session */

  val session_graph_path = Path.explode("session_graph.pdf")
  val readme_path = Path.explode("README.html")
  val files_path = Path.explode("files")

  def html_name(name: Document.Node.Name): String = Path.explode(name.theory_base_name).html.implode
  def html_path(path: Path): String = (files_path + path.squash.html).implode

  def session_relative(deps: Sessions.Deps, session0: String, session1: String): Option[String] =
  {
    for {
      info0 <- deps.sessions_structure.get(session0)
      info1 <- deps.sessions_structure.get(session1)
    } yield info0.relative_path(info1)
  }

  def node_relative(
    deps: Sessions.Deps,
    session0: String,
    node_name: Document.Node.Name): Option[String] =
  {
    val session1 = deps(session0).theory_qualifier(node_name)
    session_relative(deps, session0, session1)
  }

  def theory_link(deps: Sessions.Deps, session0: String,
    name: Document.Node.Name, body: XML.Body, anchor: Option[String] = None): Option[XML.Tree] =
  {
    val session1 = deps(session0).theory_qualifier(name)
    val info0 = deps.sessions_structure.get(session0)
    val info1 = deps.sessions_structure.get(session1)
    val fragment = if (anchor.isDefined) "#" + anchor.get else ""
    if (info0.isDefined && info1.isDefined) {
      Some(HTML.link(info0.get.relative_path(info1.get) + html_name(name) + fragment, body))
    }
    else None
  }

  def session_html(
    resources: Resources,
    session: String,
    deps: Sessions.Deps,
    db_context: Sessions.Database_Context,
    progress: Progress = new Progress,
    verbose: Boolean = false,
    html_context: HTML_Context,
    elements: Elements,
    presentation: Context,
    seen_nodes_cache: Entity_Cache = Entity_Cache.empty): Unit =
  {
    val info = deps.sessions_structure(session)
    val options = info.options
    val base = deps(session)

    val session_dir = presentation.dir(db_context.store, info)

    html_context.init_fonts(session_dir)

    Bytes.write(session_dir + session_graph_path,
      graphview.Graph_File.make_pdf(options, base.session_graph_display))

    val documents =
      for {
        doc <- info.document_variants
        document <- db_context.input_database(session)(Document_Build.read_document(_, _, doc.name))
      } yield {
        if (verbose) progress.echo("Presenting document " + session + "/" + doc.name)
        Bytes.write(session_dir + doc.path.pdf, document.pdf)
        doc
      }

    val view_links =
    {
      val deps_link =
        HTML.link(session_graph_path, HTML.text("theory dependencies"))

      val readme_links =
        if ((info.dir + readme_path).is_file) {
          Isabelle_System.copy_file(info.dir + readme_path, session_dir + readme_path)
          List(HTML.link(readme_path, HTML.text("README")))
        }
        else Nil

      val document_links =
        documents.map(doc => HTML.link(doc.path.pdf, HTML.text(doc.name)))

      Library.separate(HTML.break ::: HTML.nl,
        (deps_link :: readme_links ::: document_links).
          map(link => HTML.text("View ") ::: List(link))).flatten
    }

    def read_exports(name: Document.Node.Name): Seq[Entity] =
    {
      seen_nodes_cache.get_or_update(name, {
        if (Sessions.is_pure(name.theory_base_name)) Vector.empty
        else {
          val session1 = deps(session).theory_qualifier(name)
          val provider = Export.Provider.database_context(db_context, List(session1), name.theory)
          provider(Export.THEORY_PREFIX + "parents") match {
            case Some(_) =>
              val theory = Export_Theory.read_theory(provider, session1, name.theory)
              theory.entity_iterator.toVector
            case None =>
              progress.echo_error_message("No exports for: " + name)
              Vector.empty
          }
        }
      })
    }

    val exports = base.known_theories.map(_._2.name).map(node => node -> read_exports(node)).toMap
    val export_ranges =
      exports.view.mapValues(_.groupBy(entity =>
        Text.Range(Position.Offset.get(entity.pos), Position.End_Offset.get(entity.pos)))).toMap
    val export_names =
      exports.map {
        case (node, entities) => node.theory -> entities.map(entity => entity.name -> entity).toMap
      }

    val theories: List[XML.Body] =
    {
      var seen_files = List.empty[(Path, String, Document.Node.Name)]

      def node_file(node: Document.Node.Name): String =
        if (node.node.endsWith(".thy")) html_name(node) else html_path(Path.explode(node.node))

      def entity_anchor(
        context: Entity_Context, range: Symbol.Range, body: XML.Body): Option[XML.Elem] =
      {
        body match {
          case List(XML.Elem(Markup("span", List("id" -> _)), _)) => None
          case _ =>
            Some {
              val body1 =
                if (context.seen_ranges.contains(range)) {
                  HTML.entity_def(HTML.span(HTML.id(html_context.offset_ref(range)), body))
                }
                else HTML.span(body)
              export_ranges.get(context.node).flatMap(_.get(range)) match {
                case Some(entities) =>
                  entities.map(html_context.export_ref).foldLeft(body1) {
                    case (elem, id) =>
                      HTML.entity_def(HTML.span(HTML.id(id), List(elem)))
                  }
                case None => body1
              }
            }
        }
      }

      def entity_ref(theory: String, name: String): Option[String] =
        export_names.get(theory).flatMap(_.get(name)).map(html_context.export_ref)

      def offset_ref(context: Entity_Context, theory: String, props: Properties.T): Option[String] =
      {
        if (theory == context.node.theory) {
          for {
            offset <- Position.Def_Offset.unapply(props)
            end_offset <- Position.Def_End_Offset.unapply(props)
            range = Text.Range(offset, end_offset)
          } yield {
            context.seen_ranges += range
            html_context.offset_ref(range)
          }
        } else None
      }

      def entity_link(
        context: Entity_Context, props: Properties.T, body: XML.Body): Option[XML.Elem] =
      {
        (props, props, props, props) match {
          case (Markup.Kind(Markup.THEORY), Markup.Name(theory), Position.Def_File(thy_file), _) =>
            val node_name = resources.file_node(Path.explode(thy_file), theory = theory)
            node_relative(deps, session, node_name).map(html_dir =>
              HTML.link(html_dir + html_name(node_name), body))
          case (Markup.Ref(_), Position.Def_File(thy_file), Position.Def_Theory(def_theory),
              Markup.Name(name)) =>
            val theory = if (def_theory.nonEmpty) def_theory else context.node.theory
            val node_name = resources.file_node(Path.explode(thy_file), theory = theory)
            for {
              html_dir <- node_relative(deps, session, node_name)
              html_file = node_file(node_name)
              html_ref <- entity_ref(theory, name).orElse(offset_ref(context, theory, props))
            } yield {
              HTML.entity_ref(HTML.link(html_dir + html_file + "#" + html_ref, body))
            }
          case _ => None
        }
      }

      sealed case class Theory(
        name: Document.Node.Name,
        command: Command,
        files_html: List[(Path, XML.Tree)],
        html: XML.Tree)

      def read_theory(name: Document.Node.Name): Option[Theory] =
      {
        progress.expose_interrupt()
        if (verbose) progress.echo("Presenting theory " + name)

        for (command <- Build_Job.read_theory(db_context, resources, session, name.theory))
        yield {
          val snapshot = Document.State.init.snippet(command)

          val files_html =
            for {
              (src_path, xml) <- snapshot.xml_markup_blobs(elements = elements.html)
              if xml.nonEmpty
            }
            yield {
              progress.expose_interrupt()
              if (verbose) progress.echo("Presenting file " + src_path)

              (src_path, html_context.source(
                make_html(name, elements, entity_anchor, entity_link, xml)))
            }

          val html =
            html_context.source(
              make_html(name, elements, entity_anchor, entity_link,
                snapshot.xml_markup(elements = elements.html)))

          Theory(name, command, files_html, html)
        }
      }

      for (thy <- Par_List.map(read_theory, base.session_theories).flatten)
      yield {
        val files =
          for { (src_path, file_html) <- thy.files_html }
          yield {
            val file_name = html_path(src_path)

            seen_files.find(p => p._1 == src_path || p._2 == file_name) match {
              case None => seen_files ::= (src_path, file_name, thy.name)
              case Some((_, _, thy_name1)) =>
                error("Incoherent use of file name " + src_path + " as " + quote(file_name) +
                  " in theory " + thy_name1 + " vs. " + thy.name)
            }

            val file_path = session_dir + Path.explode(file_name)
            html_context.init_fonts(file_path.dir)

            val file_title = "File " + Symbol.cartouche_decoded(src_path.implode_short)
            HTML.write_document(file_path.dir, file_path.file_name,
              List(HTML.title(file_title)), List(html_context.head(file_title), file_html))

            List(HTML.link(file_name, HTML.text(file_title)))
          }

        val thy_title = "Theory " + thy.name.theory_base_name

        HTML.write_document(session_dir, html_name(thy.name),
          List(HTML.title(thy_title)), List(html_context.head(thy_title), thy.html))

        List(HTML.link(html_name(thy.name),
          HTML.text(thy.name.theory_base_name) :::
            (if (files.isEmpty) Nil else List(HTML.itemize(files)))))
      }
    }

    val title = "Session " + session
    HTML.write_document(session_dir, "index.html",
      List(HTML.title(title + Isabelle_System.isabelle_heading())),
      html_context.head(title, List(HTML.par(view_links))) ::
        html_context.contents("Theories", theories))
  }
}
