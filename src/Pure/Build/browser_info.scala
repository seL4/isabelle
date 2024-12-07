/*  Title:      Pure/Build/browser_info.scala
    Author:     Makarius

HTML/PDF presentation of PIDE document information.
*/

package isabelle


import scala.annotation.tailrec
import scala.collection.immutable.SortedMap
import scala.collection.mutable


object Browser_Info {
  /* browser_info store configuration */

  object Config {
    val none: Config = new Config { def enabled: Boolean = false }
    val standard: Config = new Config { def enabled: Boolean = true }

    def dir(path: Path): Config =
      new Config {
        def enabled: Boolean = true
        override def presentation_dir(store: Store): Path = path
      }

    def make(s: String): Config =
      if (s == ":") standard else dir(Path.explode(s))
  }

  abstract class Config private {
    def enabled: Boolean
    def enabled(info: Sessions.Info): Boolean = enabled || info.browser_info
    def presentation_dir(store: Store): Path = store.presentation_dir
  }


  /* meta info within the file-system */

  object Meta_Info {
    /* directory */

    val PATH: Path = Path.explode(".browser_info")

    def check_directory(dir: Path): Unit = {
      if (dir.is_dir && !(dir + PATH).is_dir && File.read_dir(dir).nonEmpty) {
        error("Existing content in " + dir.expand + " lacks " + PATH + " meta info.\n" +
          "To avoid potential disaster, it has not been changed automatically.\n" +
          "If this is the intended directory, please move/remove/empty it manually.")
      }
    }

    def init_directory(dir: Path): Path = {
      check_directory(dir)
      Isabelle_System.make_directory(dir + PATH)
      dir
    }

    def clean_directory(dir: Path): Path = {
      check_directory(dir)
      Isabelle_System.rm_tree(dir)  // guarded by check_directory!
      Isabelle_System.new_directory(dir + PATH)
    }


    /* content */

    def make_path(dir: Path, name: String): Path =
      dir + PATH + Path.basic(name)

    def value(dir: Path, name: String): String = {
      val path = make_path(dir, name)
      if (path.is_file) File.read(path) else ""
    }

    def change(dir: Path, name: String)(f: String => String): Unit = {
      val path = make_path(dir, name)
      val x = value(dir, name)
      val y =
        try { f(x) }
        catch { case ERROR(msg) => error("Failed to change " + path.expand + ":\n" + msg)}
      if (x != y) File.write(path, y)
    }


    /* build_uuid */

    val BUILD_UUID = "build_uuid"

    def check_build_uuid(dir: Path, uuid: String): Boolean = {
      val uuid0 = value(dir, BUILD_UUID)
      uuid0.nonEmpty && uuid.nonEmpty && uuid0 == uuid
    }

    def set_build_uuid(dir: Path, uuid: String): Unit =
      change(dir, BUILD_UUID)(_ => uuid)


    /* index */

    val INDEX = "index.json"

    object Item {
      def parse(json: JSON.T): Item = {
        def err(): Nothing =
          error("Bad JSON object for item:\n" + JSON.Format.pretty_print(json))
        val obj = JSON.Object.unapply(json) getOrElse err()

        val name = JSON.string(obj, "name") getOrElse err()
        val description = JSON.string(obj, "description") getOrElse ""
        Item(name, description = Symbol.trim_blank_lines(description))
      }
    }

    sealed case class Item(name: String, description: String = "") {
      override def toString: String = name

      def json: JSON.T = JSON.Object("name" -> name, "description" -> description)
    }

    object Index {
      def parse(s: JSON.S, kind: String): Index = {
        if (s.isEmpty) Index(kind, Nil)
        else {
          def err(): Nothing = error("Bad JSON object " + kind + " index:\n" + s)

          val json = JSON.parse(s)
          val obj = JSON.Object.unapply(json) getOrElse err()

          val kind1 = JSON.string(obj, "kind") getOrElse err()
          val items = JSON.list(obj, "items", x => Some(Item.parse(x))) getOrElse err()
          if (kind == kind1) Index(kind, items)
          else error("Expected index kind " + quote(kind) + " but found " + quote(kind1))
        }
      }
    }

    sealed case class Index(kind: String, items: List[Item]) {
      def is_empty: Boolean = items.isEmpty

      def + (item: Item): Index =
        Index(kind, (item :: items.filterNot(_.name == item.name)).sortBy(_.name))

      def json: JSON.T = JSON.Object("kind" -> kind, "items" -> items.map(_.json))
      def print_json: JSON.S = JSON.Format.pretty_print(json)
    }
  }


  /* presentation elements */

  sealed case class Elements(
    html: Markup.Elements = Markup.Elements.empty,
    entity: Markup.Elements = Markup.Elements.empty,
    language: Markup.Elements = Markup.Elements.empty)

  val default_elements: Elements =
    Elements(
      html = Rendering.foreground_elements ++ Rendering.text_color_elements +
        Markup.NUMERAL + Markup.COMMENT + Markup.ENTITY + Markup.LANGUAGE +
        Markup.PATH + Markup.URL,
      entity = Markup.Elements(Markup.THEORY, Markup.TYPE_NAME, Markup.CONSTANT, Markup.FACT,
        Markup.CLASS, Markup.LOCALE, Markup.FREE))

  val extra_elements: Elements =
    Elements(
      html = default_elements.html ++ Rendering.markdown_elements,
      language = Markup.Elements(Markup.Language.DOCUMENT))



  /** HTML/PDF presentation context **/

  def context(
    sessions_structure: Sessions.Structure,
    elements: Elements = default_elements,
    root_dir: Path = Path.current,
    document_info: Document_Info = Document_Info.empty
  ): Context = new Context(sessions_structure, elements, root_dir, document_info)

  class Context private[Browser_Info](
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

    def session_chapter(session: String): String =
      sessions_structure(session).chapter

    def chapter_dir(session: String): Path =
      root_dir + Path.basic(session_chapter(session))

    def session_dir(session: String): Path =
      chapter_dir(session) + Path.basic(session)

    def theory_dir(theory: Document_Info.Theory): Path =
      session_dir(theory.dynamic_session)

    def theory_html(theory: Document_Info.Theory): Path =
    {
      def check(name: String): Option[Path] = {
        val path = Path.basic(name).html
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


    /* preview PIDE document */

    lazy val isabelle_css: String = File.read(HTML.isabelle_css)

    def html_document(title: String, body: XML.Body, fonts_css: String): HTML_Document = {
      val content =
        HTML.output_document(
          List(
            HTML.style(fonts_css + "\n\n" + isabelle_css),
            HTML.title(title)),
          List(HTML.source(body)), css = "", structural = false)
      HTML_Document(title, content)
    }

    def preview_document(
      snapshot: Document.Snapshot,
      plain_text: Boolean = false,
      fonts_css: String = HTML.fonts_css()
    ): HTML_Document = {
      require(!snapshot.is_outdated, "document snapshot outdated")

      val name = snapshot.node_name
      if (plain_text) {
        val title = "File " + Symbol.cartouche_decoded(name.file_name)
        val body = HTML.text(snapshot.node.source)
        html_document(title, body, fonts_css)
      }
      else {
        Resources.html_document(snapshot) getOrElse {
          val title =
            if (name.is_theory) "Theory " + quote(name.theory_base_name)
            else "File " + Symbol.cartouche_decoded(name.file_name)
          val xml = snapshot.xml_markup(elements = elements.html)
          val body = Node_Context.empty.make_html(elements, xml)
          html_document(title, body, fonts_css)
        }
      }
    }


    /* maintain presentation structure */

    def update_chapter(session_name: String, session_description: String): Unit = synchronized {
      val dir = Meta_Info.init_directory(chapter_dir(session_name))
      Meta_Info.change(dir, Meta_Info.INDEX) { text =>
        val index0 = Meta_Info.Index.parse(text, "chapter")
        val item = Meta_Info.Item(session_name, description = session_description)
        val index = index0 + item

        if (index != index0) {
          val title = "Isabelle/" + session_chapter(session_name) + " sessions"
          HTML.write_document(dir, "index.html",
            List(HTML.title(title + Isabelle_System.isabelle_heading())),
            HTML.chapter(title) ::
              (if (index.is_empty) Nil
              else
                List(HTML.div("sessions",
                  List(HTML.description(
                    index.items.map(item =>
                      (List(HTML.link(item.name + "/index.html", HTML.text(item.name))),
                        if (item.description.isEmpty) Nil
                        else HTML.break ::: List(HTML.pre(HTML.text(item.description)))))))))),
            root = Some(root_dir))
        }

        index.print_json
      }
    }

    def update_root(): Unit = synchronized {
      Meta_Info.init_directory(root_dir)
      HTML.init_fonts(root_dir)
      Isabelle_System.copy_file(Path.explode("~~/lib/logo/isabelle.gif"),
        root_dir + Path.explode("isabelle.gif"))

      Meta_Info.change(root_dir, Meta_Info.INDEX) { text =>
        val index0 = Meta_Info.Index.parse(text, "root")
        val index = {
          val items1 =
            sessions_structure.known_chapters
              .map(ch => Meta_Info.Item(ch.name, description = ch.description))
          val items2 = index0.items.filterNot(item => items1.exists(_.name == item.name))
          index0.copy(items = items1 ::: items2)
        }

        if (index != index0) {
          val title = "The " + XML.text(Isabelle_System.isabelle_name()) + " Library"
          HTML.write_document(root_dir, "index.html",
            List(HTML.title(title + Isabelle_System.isabelle_heading())),
            HTML.chapter(title) ::
              (if (index.is_empty) Nil
              else
                List(HTML.div("sessions",
                  List(HTML.description(
                    index.items.map(item =>
                      (List(HTML.link(item.name + "/index.html", HTML.text(item.name))),
                        if (item.description.isEmpty) Nil
                        else HTML.break ::: List(HTML.pre(HTML.text(item.description)))))))))),
            root = Some(root_dir))
        }

        index.print_json
      }
    }
  }

  sealed case class HTML_Document(title: String, content: String)


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
      context: Context,
      session_name: String,
      theory_name: String,
      file_name: String,
      node_dir: Path,
    ): Node_Context =
      new Node_Context {
        private val seen_ranges: mutable.Set[Symbol.Range] = mutable.Set.empty

        override def make_def(range: Symbol.Range, body: XML.Body): Option[XML.Elem] =
          body match {
            case List(XML.Elem(Markup("span", List("id" -> _)), _)) => None
            case _ =>
              for (theory <- context.theory_by_name(session_name, theory_name))
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

        override def make_file_ref(file: String, body: XML.Body): Option[XML.Elem] = {
          for (theory <- context.theory_by_file(session_name, file))
          yield {
            val html_path = context.theory_dir(theory) + context.smart_html(theory, file)
            val html_link = HTML.relative_href(html_path, base = Some(node_dir))
            HTML.link(html_link, body)
          }
        }

        override def make_ref(props: Properties.T, body: XML.Body): Option[XML.Elem] = {
          props match {
            case Theory_Ref(thy_name) =>
              for (theory <- context.theory_by_name(session_name, thy_name))
              yield {
                val html_path = context.theory_dir(theory) + context.theory_html(theory)
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
                theory <- context.theory_by_file(session_name, def_file)
                html_ref <- logical_ref(theory) orElse physical_ref(theory)
              }
              yield {
                val html_path = context.theory_dir(theory) + context.smart_html(theory, def_file)
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
    def make_file_ref(file: String, body: XML.Body): Option[XML.Elem] = None

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
          case XML.Elem(Markup.Path(file), body) =>
            val (body1, offset) = html_body(body, end_offset)
            make_file_ref(file, body1) match {
              case Some(link) => (List(link), offset)
              case None => (body1, offset)
            }
          case XML.Elem(Markup.Url(href), body) =>
            val (body1, offset) = html_body(body, end_offset)
            (List(HTML.link(href, body1)), offset)
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
            Rendering.foreground.get(name) orElse Rendering.get_text_color(name) match {
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



  /** build presentation **/

  val session_graph_path: Path = Path.explode("session_graph.pdf")

  def build_session(
    context: Context,
    session_context: Export.Session_Context,
    progress: Progress = new Progress,
  ): Unit = {
    progress.expose_interrupt()

    val session_name = session_context.session_name
    val session_info = session_context.sessions_structure(session_name)

    val session_dir = context.session_dir(session_name).expand
    progress.echo("Presenting " + session_name + " in " + session_dir + " ...")

    Meta_Info.init_directory(context.chapter_dir(session_name))
    Meta_Info.clean_directory(session_dir)

    val session = context.document_info.the_session(session_name)

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
        progress.echo("Presenting document " + session_name + "/" + doc.name, verbose = true)
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

      val snapshot = Build.read_theory(session_context.theory(theory_name)) getOrElse err()
      val theory = context.theory_by_name(session_name, theory_name) getOrElse err()

      progress.echo("Presenting theory " + quote(theory_name), verbose = true)

      val thy_elements = theory.elements(context.elements)

      def node_context(file_name: String, node_dir: Path): Node_Context =
        Node_Context.make(context, session_name, theory_name, file_name, node_dir)

      val thy_html =
        context.source(
          node_context(theory.thy_file, session_dir).
            make_html(thy_elements, snapshot.xml_markup(elements = thy_elements.html)))

      val master_dir = Path.explode(snapshot.node_name.master_dir)

      val files =
        for {
          blob_name <- snapshot.node_files.tail
          xml = snapshot.switch(blob_name).xml_markup(elements = thy_elements.html)
          if xml.nonEmpty
        }
        yield {
          progress.expose_interrupt()

          val file = blob_name.node
          progress.echo("Presenting file " + quote(file), verbose = true)

          val file_html = session_dir + context.file_html(file)
          val file_dir = file_html.dir
          val html_link = HTML.relative_href(file_html, base = Some(session_dir))
          val html = context.source(node_context(file, file_dir).make_html(thy_elements, xml))

          val path = Path.explode(file)
          val src_path = File.relative_path(master_dir, path).getOrElse(path)

          val file_title = "File " + Symbol.cartouche_decoded(src_path.implode_short)
          HTML.write_document(file_dir, file_html.file_name,
            List(HTML.title(file_title)), List(context.head(file_title), html),
            root = Some(context.root_dir))
          List(HTML.link(html_link, HTML.text(file_title)))
        }

      val thy_title = "Theory " + theory.print_short
      HTML.write_document(session_dir, context.theory_html(theory).implode,
        List(HTML.title(thy_title)), List(context.head(thy_title), thy_html),
        root = Some(context.root_dir))

      List(HTML.link(context.theory_html(theory),
        HTML.text(theory.print_short) :::
        (if (files.isEmpty) Nil else List(HTML.itemize(files)))))
    }

    val theories = session.used_theories.map(present_theory)

    val title = "Session " + session_name
      HTML.write_document(session_dir, "index.html",
        List(HTML.title(title + Isabelle_System.isabelle_heading())),
        context.head(title, List(HTML.par(document_links))) ::
          context.contents("Theories", theories),
        root = Some(context.root_dir))

    Meta_Info.set_build_uuid(session_dir, session.build_uuid)

    context.update_chapter(session_name, session_info.description)
  }

  def build(
    browser_info: Config,
    store: Store,
    deps: Sessions.Deps,
    sessions: List[String],
    progress: Progress = new Progress,
    server: SSH.Server = SSH.no_server
  ): Unit = {
    val root_dir = browser_info.presentation_dir(store).absolute
    progress.echo("Presentation in " + root_dir)

    using(Export.open_database_context(store, server = server)) { database_context =>
      val context0 = context(deps.sessions_structure, root_dir = root_dir)

      val sessions1 =
        deps.sessions_structure.build_requirements(sessions).filter { session_name =>
          using(database_context.open_database(session_name)) { session_database =>
            database_context.store.read_build(session_database.db, session_name) match {
              case None => false
              case Some(build) =>
                val session_dir = context0.session_dir(session_name)
                !Meta_Info.check_build_uuid(session_dir, build.uuid)
            }
          }
        }

      val context1 =
        context(deps.sessions_structure, root_dir = root_dir,
          document_info = Document_Info.read(database_context, deps, sessions1))

      context1.update_root()

      Par_List.map({ (session: String) =>
        using(database_context.open_session(deps.background(session))) { session_context =>
          build_session(context1, session_context, progress = progress)
        }
      }, sessions1)
    }
  }
}
