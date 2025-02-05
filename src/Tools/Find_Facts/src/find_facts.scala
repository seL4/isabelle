/*  Title:      Tools/Find_Facts/src/find_facts.scala
    Author:     Fabian Huch, TU Muenchen

Full-text search engine for Isabelle (including web server), using Apache Solr
https://solr.apache.org as backend.
*/

package isabelle.find_facts


import isabelle._

import scala.annotation.tailrec
import scala.collection.immutable.TreeMap
import scala.collection.mutable


object Find_Facts {
  /** blocks **/

  object Kind {
    val CONST = "constant"
    val TYPE = "type"
    val THM = "fact"
  }

  case class Block(
    id: String,
    version: Long,
    chapter: String,
    session: String,
    theory: String,
    file: String,
    url_path: Path,
    command: String,
    start_line: Int,
    src_before: String,
    src: String,
    src_after: String,
    xml: XML.Body,
    html: String,
    entity_kname: Option[String],
    consts: List[String],
    typs: List[String],
    thms: List[String]
  ) {
    def path = Path.explode(file)
    def file_type: String = path.get_ext
    def file_name: String = path.file_name

    def kinds: List[String] =
      (if (typs.nonEmpty) List(Kind.TYPE) else Nil) :::
      (if (consts.nonEmpty) List(Kind.CONST) else Nil) :::
      (if (thms.nonEmpty) List(Kind.THM) else Nil)
    def names: List[String] = (typs ::: consts ::: thms).distinct
  }

  case class Blocks(num_found: Long, blocks: List[Block], cursor: String)


  /** queries */

  enum Atom {
    case Exact(s: String) extends Atom
    case Value(s: String) extends Atom
  }

  enum Field {
    case chapter, session, file_type, theory, command, source, names, consts, typs, thms, kinds
  }

  sealed trait Filter
  case class Field_Filter(field: Field, either: List[Atom]) extends Filter
  case class Any_Filter(either: List[Atom]) extends Filter {
    def fields: List[Field] = List(Field.session, Field.theory, Field.source, Field.names)
  }

  case class Select(field: Field, values: List[String])

  object Query {
    def apply(filters: Filter*): Query = new Query(filters.toList)
  }

  case class Query(
    filters: List[Filter] = Nil,
    exclude: List[Filter] = Nil,
    selects: List[Select] = Nil)


  /* stats and facets */

  case class Stats(
    results: Long,
    sessions: Long,
    theories: Long,
    commands: Long,
    consts: Long,
    typs: Long,
    thms: Long)

  case class Facets(
    chapter: Map[String, Long],
    session: Map[String, Long],
    theory: Map[String, Long],
    file_type: Map[String, Long],
    command: Map[String, Long],
    kinds: Map[String, Long],
    consts: Map[String, Long],
    typs: Map[String, Long],
    thms: Map[String, Long])


  /** Solr data model **/

  val solr_data_dir: Path = Path.explode("$FIND_FACTS_HOME_USER/solr")

  object private_data extends Solr.Data("find_facts") {
    /* types */

    val symbol_codes =
      for {
        entry <- Symbol.symbols.entries
        code <- entry.decode.toList
        input <- entry.symbol :: entry.abbrevs
      } yield input -> code

    val replacements =
      for ((symbol, codes) <- symbol_codes.groupMap(_._1)(_._2).toList if codes.length == 1)
      yield symbol -> Library.the_single(codes)

    val Special_Char = """(.*[(){}\[\].,:"].*)""".r
    val Arrow = """(.*=>.*)""".r

    val synonyms =
      for {
        (symbol, code) <- symbol_codes
        if !Special_Char.matches(symbol) && !Arrow.matches(symbol)
      } yield symbol + " => " + code

    override lazy val more_config = Map(Path.basic("synonyms.txt") -> synonyms.mkString("\n"))

    object Types {
      private val strip_html = Solr.Class("charFilter", "HTMLStripCharFilterFactory")
      private val replace_symbol_chars =
        replacements.collect {
          case (Special_Char(pattern), code) =>
            Solr.Class(
              "charFilter", "PatternReplaceCharFilterFactory",
              List("pattern" -> ("\\Q" + pattern + "\\E"), "replacement" -> code))
        }

      private val symbol_pattern =
         """\s*(::|[(){}\[\].,:"]|[^\p{ASCII}]|((?![^\p{ASCII}])[^(){}\[\].,:"\s])+)\s*""".r

      private val tokenize =
        Solr.Class("tokenizer", "WhitespaceTokenizerFactory", List("rule" -> "java"))
      private val tokenize_symbols =
        Solr.Class("tokenizer", "PatternTokenizerFactory",
          List("pattern" -> symbol_pattern.toString, "group" -> "1"))

      private val to_lower = Solr.Class("filter", "LowerCaseFilterFactory")
      private val add_ascii =
        Solr.Class("filter", "ASCIIFoldingFilterFactory", List("preserveOriginal" -> "true"))
      private val delimit_words =
        Solr.Class("filter", "WordDelimiterGraphFilterFactory", List(
          "splitOnCaseChange" -> "0", "stemEnglishPossessive" -> "0", "preserveOriginal" -> "1"))
      private val flatten = Solr.Class("filter", "FlattenGraphFilterFactory")
      private val replace_symbols =
        Solr.Class("filter", "SynonymGraphFilterFactory", List("synonyms" -> "synonyms.txt"))
      private val replace_special_symbols =
        replacements.collect {
          case (Arrow(arrow), code) =>
            Solr.Class("filter", "PatternReplaceFilterFactory",
              List("pattern" -> ("\\Q" + arrow + "\\E"), "replacement" -> code))
        }

      val source =
        Solr.Type("name", "TextField", Nil, List(
          XML.Elem(Markup("analyzer", List("type" -> "index")),
            List(strip_html, tokenize_symbols, to_lower, add_ascii, delimit_words, flatten)),
          XML.Elem(
            Markup("analyzer", List("type" -> "query")),
              replace_symbol_chars ::: tokenize_symbols :: replace_symbols ::
                replace_special_symbols ::: to_lower :: Nil)))

      val name =
        Solr.Type("source", "TextField", Nil, List(
          XML.Elem(Markup("analyzer", List("type" -> "index")),
            List(tokenize, to_lower, delimit_words, flatten)),
          XML.Elem(Markup("analyzer", List("type" -> "query")), List(tokenize, to_lower))))

      val text = Solr.Type("text", "TextField")
    }


    /* fields */

    object Fields {
      val id = Solr.Field("id", Solr.Type.string).make_unique_key
      val version = Solr.Field("version", Solr.Type.long, Solr.Column_Wise(true))
      val chapter = Solr.Field("chapter", Solr.Type.string, Solr.Column_Wise(true))
      val session = Solr.Field("session", Types.name)
      val session_facet = Solr.Field("session_facet", Solr.Type.string, Solr.Stored(false))
      val theory = Solr.Field("theory", Types.name)
      val theory_facet = Solr.Field("theory_facet", Solr.Type.string, Solr.Stored(false))
      val file = Solr.Field("file", Solr.Type.string, Solr.Indexed(false))
      val file_type =
        Solr.Field("file_type", Solr.Type.string, Solr.Column_Wise(true) ::: Solr.Stored(false))
      val url_path = Solr.Field("url_path", Solr.Type.string, Solr.Indexed(false))
      val command = Solr.Field("command", Solr.Type.string, Solr.Column_Wise(true))
      val start_line = Solr.Field("start_line", Solr.Type.int, Solr.Column_Wise(true))
      val src_before = Solr.Field("src_before", Solr.Type.string, Solr.Indexed(false))
      val src_after = Solr.Field("src_after", Solr.Type.string, Solr.Indexed(false))
      val src = Solr.Field("src", Types.source)
      val xml = Solr.Field("xml", Solr.Type.bytes, Solr.Indexed(false))
      val html = Solr.Field("html", Solr.Type.bytes, Solr.Indexed(false))
      val entity_kname = Solr.Field("entity_kname", Solr.Type.string, Solr.Indexed(false))
      val consts = Solr.Field("consts", Types.name, Solr.Multi_Valued(true))
      val consts_facet =
        Solr.Field("consts_facet", Solr.Type.string, Solr.Multi_Valued(true) ::: Solr.Stored(false))
      val typs = Solr.Field("typs", Types.name, Solr.Multi_Valued(true))
      val typs_facet =
        Solr.Field("typs_facet", Solr.Type.string, Solr.Multi_Valued(true) ::: Solr.Stored(false))
      val thms = Solr.Field("thms", Types.name, Solr.Multi_Valued(true))
      val thms_facet =
        Solr.Field("thms_facet", Solr.Type.string, Solr.Multi_Valued(true) ::: Solr.Stored(false))
      val names = Solr.Field("names", Types.name, Solr.Multi_Valued(true) ::: Solr.Stored(false))
      val kinds =
        Solr.Field("kinds", Solr.Type.string,
          Solr.Multi_Valued(true) ::: Solr.Column_Wise(true) ::: Solr.Stored(false))
    }

    lazy val fields: Solr.Fields = Solr.Fields(
      Fields.id, Fields.version, Fields.chapter, Fields.session, Fields.session_facet,
      Fields.theory, Fields.theory_facet, Fields.file, Fields.file_type, Fields.url_path,
      Fields.command, Fields.start_line, Fields.src_before, Fields.src_after, Fields.src,
      Fields.xml, Fields.html, Fields.entity_kname, Fields.consts, Fields.consts_facet, Fields.typs,
      Fields.typs_facet, Fields.thms, Fields.thms_facet, Fields.names, Fields.kinds)


    /* operations */

    def read_domain(db: Solr.Database, q: Solr.Source): Set[String] =
      db.execute_query(Fields.id, List(Fields.id), None, 100000,
        { results =>
          results.map(_.string(Fields.id)).toSet
        }, q = q)

    def read_block(res: Solr.Result): Block = {
      val id = res.string(Fields.id)
      val version = res.long(Fields.version)
      val chapter = res.string(Fields.chapter)
      val session = res.string(Fields.session)
      val theory = res.string(Fields.theory)
      val file = res.string(Fields.file)
      val url_path = Path.explode(res.string(Fields.url_path))
      val command = res.string(Fields.command)
      val start_line = res.int(Fields.start_line)
      val src_before = res.string(Fields.src_before)
      val src = res.string(Fields.src)
      val src_after = res.string(Fields.src_after)
      val xml = YXML.parse_body(res.bytes(Fields.xml))
      val html = res.bytes(Fields.html).text
      val entity_kname = res.get_string(Fields.entity_kname)
      val consts = res.list_string(Fields.consts)
      val typs = res.list_string(Fields.typs)
      val thms = res.list_string(Fields.thms)

      Block(id = id, version = version, chapter = chapter, session = session, theory = theory,
        file = file, url_path = url_path, command = command, start_line = start_line, src_before =
        src_before, src = src, src_after = src_after, xml = xml, html = html, entity_kname =
        entity_kname, consts = consts, typs = typs, thms = thms)
    }

    def read_blocks(
      db: Solr.Database,
      q: Solr.Source,
      fq: List[Solr.Source],
      cursor: Option[String] = None,
      max_results: Int = 10
    ): Blocks =
      db.execute_query(Fields.id, stored_fields, cursor, max_results,
        { results =>
          val next_cursor = results.next_cursor
          val blocks = results.map(read_block).toList
          Blocks(results.num_found, blocks, next_cursor)
        }, q = q, fq = fq, more_chunks = 0)

    def stream_blocks(
      db: Solr.Database,
      q: Solr.Source,
      stream: Iterator[Block] => Unit,
      cursor: Option[String] = None,
    ): Unit =
      db.execute_query(Fields.id, stored_fields, cursor, 10000,
        { results =>
          stream(results.map(read_block))
        }, q = q)

    def update_theory(db: Solr.Database, theory_name: String, blocks: List[Block]): Unit =
      db.transaction {
        val delete =
          read_domain(db, Solr.filter(Fields.theory, Solr.phrase(theory_name))) -- blocks.map(_.id)

        if (delete.nonEmpty) db.execute_batch_delete(delete.toList)

        db.execute_batch_insert(
          for (block <- blocks) yield { (doc: Solr.Document) =>
            doc.string(Fields.id) = block.id
            doc.long(Fields.version) = block.version
            doc.string(Fields.chapter) = block.chapter
            doc.string(Fields.session) = block.session
            doc.string(Fields.session_facet) = block.session
            doc.string(Fields.theory) = block.theory
            doc.string(Fields.theory_facet) = block.theory
            doc.string(Fields.file) = block.file
            doc.string(Fields.file_type) = block.file_type
            doc.string(Fields.url_path) = block.url_path.implode
            doc.string(Fields.command) = block.command
            doc.int(Fields.start_line) = block.start_line
            doc.string(Fields.src_before) = block.src_before
            doc.string(Fields.src) = block.src
            doc.string(Fields.src_after) = block.src_after
            doc.bytes(Fields.xml) = YXML.bytes_of_body(block.xml)
            doc.bytes(Fields.html) = Bytes(block.html)
            doc.string(Fields.entity_kname) = block.entity_kname
            doc.string(Fields.consts) = block.consts
            doc.string(Fields.consts_facet) = block.consts
            doc.string(Fields.typs) = block.typs
            doc.string(Fields.typs_facet) = block.typs
            doc.string(Fields.thms) = block.thms
            doc.string(Fields.thms_facet) = block.thms
            doc.string(Fields.names) = block.names
            doc.string(Fields.kinds) = block.kinds
          })
      }

    def read_theory(db: Solr.Database, theory_name: String): List[Block] = {
      val blocks = new mutable.ListBuffer[Block]
      stream_blocks(db, Solr.filter(Fields.theory_facet, Solr.phrase(theory_name)), {
        res => blocks ++= res
      })
      blocks.toList
    }

    def delete_session(db: Solr.Database, session_name: String): Unit =
      db.transaction {
        val delete = read_domain(db, Solr.filter(Fields.session, Solr.phrase(session_name)))
        if (delete.nonEmpty) db.execute_batch_delete(delete.toList)
      }

    def query_stats(db: Solr.Database, q: Solr.Source, fq: List[Solr.Source]): Stats =
      db.execute_stats_query(
        List(Fields.session_facet, Fields.theory_facet, Fields.command, Fields.consts_facet,
          Fields.typs_facet, Fields.thms_facet, Fields.start_line),
        { res =>
          val results = res.count
          val sessions = res.count(Fields.session_facet)
          val theories = res.count(Fields.theory_facet)
          val commands = res.count(Fields.theory_facet)
          val consts = res.count(Fields.consts_facet)
          val typs = res.count(Fields.typs_facet)
          val thms = res.count(Fields.thms_facet)

          Stats(results, sessions, theories, commands, consts, typs, thms)
        }, q = q, fq = fq)

    def query_facets(
      db: Solr.Database,
      q: Solr.Source,
      fq: List[Solr.Source],
      max_terms: Int = 100
    ): Facets =
      db.execute_facet_query(
        List(Fields.chapter, Fields.session_facet, Fields.theory_facet, Fields.file_type,
          Fields.command, Fields.kinds, Fields.consts_facet, Fields.typs_facet, Fields.thms_facet),
        { res =>
          val chapter = res.string(Fields.chapter)
          val sessions = res.string(Fields.session_facet)
          val theories = res.string(Fields.theory_facet)
          val file_types = res.string(Fields.file_type)
          val commands = res.string(Fields.command)
          val kinds = res.string(Fields.kinds)
          val consts = res.string(Fields.consts_facet)
          val typs = res.string(Fields.typs_facet)
          val thms = res.string(Fields.thms_facet)

          Facets(chapter, sessions, theories, file_types, commands, kinds, consts, typs, thms)
        }, q = q, fq = fq, max_terms = max_terms)


    /* queries */

    def solr_field(field: Field, select: Boolean = false): Solr.Field =
      field match {
        case Field.chapter => Fields.chapter
        case Field.session if select => Fields.session_facet
        case Field.session => Fields.session
        case Field.theory if select => Fields.theory_facet
        case Field.theory => Fields.theory
        case Field.file_type => Fields.file_type
        case Field.command => Fields.command
        case Field.source => Fields.src
        case Field.names => Fields.names
        case Field.consts if select => Fields.consts_facet
        case Field.consts => Fields.consts
        case Field.typs if select => Fields.typs_facet
        case Field.typs => Fields.typs
        case Field.thms if select => Fields.thms_facet
        case Field.thms => Fields.thms
        case Field.kinds => Fields.kinds
      }

    def solr_query(query: Query): (Solr.Source, List[Solr.Source]) = {
      def solr_atom(atom: Atom): List[Solr.Source] =
        atom match {
          case Atom.Value(s) if s.isEmpty => Nil
          case Atom.Value(s) if !s.exists(Solr.wildcard_char(_)) => List(Solr.term(s))
          case Atom.Value(s) =>
            val terms = s.split("\\s+").toList.filterNot(_.isBlank)
            if (terms.isEmpty) Nil else terms.map(Solr.wildcard)
          case Atom.Exact(s) => List(Solr.phrase(s))
        }

      def solr_atoms(field: Field, atoms: List[Atom]): List[Solr.Source] =
        for {
          atom <- atoms
          source <- solr_atom(atom)
        } yield Solr.filter(solr_field(field), source)

      def solr_filter(filter: Filter): List[Solr.Source] =
        filter match {
          case Field_Filter(field, atoms) => solr_atoms(field, atoms)
          case any@Any_Filter(atoms) => any.fields.flatMap(solr_atoms(_, atoms))
        }

      def solr_select(select: Select): Solr.Source = {
        val field = solr_field(select.field, select = true)
        Solr.tag(field.name, Solr.filter(field, Solr.OR(select.values.map(Solr.phrase))))
      }

      val filter = query.filters.map(filter => Solr.OR(solr_filter(filter)))
      val exclude = query.exclude.flatMap(solr_filter).map(Solr.exclude)
      val selects = query.selects.map(solr_select)

      (Solr.AND(filter ::: exclude), selects)
    }
  }

  def query_block(db: Solr.Database, id: String): Option[Block] = {
    val q = Solr.filter(Find_Facts.private_data.Fields.id, Solr.phrase(id))
    Find_Facts.private_data.read_blocks(db, q, Nil).blocks.headOption
  }

  def query_blocks(db: Solr.Database, query: Query, cursor: Option[String] = None): Blocks = {
    val (q, fq) = Find_Facts.private_data.solr_query(query)
    Find_Facts.private_data.read_blocks(db, q, fq, cursor = cursor)
  }

  def query_stats(db: Solr.Database, query: Query): Stats = {
    val (q, fq) = Find_Facts.private_data.solr_query(query)
    Find_Facts.private_data.query_stats(db, q, fq)
  }

  def query_facet(db: Solr.Database, query: Query): Facets = {
    val (q, fq) = Find_Facts.private_data.solr_query(query)
    Find_Facts.private_data.query_facets(db, q, fq)
  }


  /** indexing **/

  def make_thy_blocks(
    options: Options,
    session: Session,
    browser_info_context: Browser_Info.Context,
    document_info: Document_Info,
    theory_context: Export.Theory_Context,
    snapshot: Document.Snapshot,
    chapter: String
  ): List[Block] = {
    val theory = theory_context.theory
    val entities = Export_Theory.read_theory(theory_context).entity_iterator.toList
    val session_name = theory_context.session_context.session_name

    val theory_info =
      document_info.theory_by_name(session_name, theory).getOrElse(
        error("No info for theory " + theory))
    val thy_dir = browser_info_context.theory_dir(theory_info)

    def make_node_blocks(
      snapshot: Document.Snapshot,
      command_ranges: List[(String, Text.Range)]
    ): List[Block] = {
      val version = snapshot.version.id
      val file = Path.explode(snapshot.node_name.node).squash.implode
      val url_path = thy_dir + browser_info_context.smart_html(theory_info, snapshot.node_name.node)

      val elements =
        Browser_Info.Elements(html = Browser_Info.default_elements.html - Markup.ENTITY)
      val node_context = Browser_Info.Node_Context.empty

      val content = XML.content(snapshot.xml_markup(elements = Markup.Elements.empty))
      def get_content(range: Text.Range): String =
        Symbol.decode(Line.normalize(range.substring(content)))

      val document = Line.Document(content.replace('\r', '\u001a'))
      val num_lines = document.lines.length
      def content_range(start: Line.Position, stop: Line.Position): Text.Range =
        Text.Range(document.offset(start).get, document.offset(stop).get)

      val index = Symbol.Index(content)
      val node_entities =
        TreeMap.from(entities
          .filter(entity => entity.file == snapshot.node_name.node)
          .groupBy(entity => index.decode(entity.range).start))

      val rendering = new Rendering(snapshot, options, session)
      val comment_ranges = rendering.comments(Text.Range.full).map(markup => ("", markup.range))

      for ((command, range) <- command_ranges ::: comment_ranges) yield {
        val line_range = document.range(range)
        val start_line = line_range.start.line1

        val id = file + "|" + range.start + ".." + range.stop

        val src_before = get_content(
          content_range(Line.Position((line_range.start.line - 5).max(0)), line_range.start))
        val src = get_content(range)
        val src_after = get_content(
          content_range(line_range.stop, Line.Position((line_range.stop.line + 5).min(num_lines))))

        val xml = snapshot.xml_markup(range, elements = elements.html)
        val html =
          HTML.output(node_context.make_html(elements, xml), hidden = true, structural = false)

        val entities = node_entities.range(range.start, range.stop).values.toList.flatten.distinct

        def get_entities(kind: String): List[String] =
          for {
            entity <- entities
            if entity.export_kind == kind
            if range.contains(index.decode(entity.range))
          } yield entity.name

        val entity_kname = entities.sortBy(_.name.length).headOption.map(_.kname)

        val typs = get_entities(Export_Theory.Kind.TYPE)
        val consts = get_entities(Export_Theory.Kind.CONST)
        val thms = get_entities(Export_Theory.Kind.THM)

        Block(id = id, version = version, chapter = chapter, session = session_name, theory =
          theory, file = file, url_path = url_path, command = command, start_line = start_line,
          src_before = src_before, src = src, src_after = src_after, xml = xml, html = html,
          entity_kname = entity_kname, consts = consts, typs = typs, thms = thms)
      }
    }

    def expand_block(block: Thy_Blocks.Block): List[Thy_Blocks.Block] =
      block match {
        case Thy_Blocks.Thy(inner) => inner.flatMap(expand_block)
        case e@Thy_Blocks.Decl(inner) =>
          val inner1 = inner.flatMap(expand_block)
          if (inner.length > 1) e :: inner1 else List(e)
        case _ => List(block)
      }

    val thy_command_ranges =
      for (block <- Thy_Blocks.read_blocks(snapshot).flatMap(expand_block))
      yield (block.command, block.range)

    make_node_blocks(snapshot, thy_command_ranges) :::
      (for {
        blob_name <- snapshot.node_files.tail
        snapshot1 = snapshot.switch(blob_name)
        if snapshot1.node.source_wellformed
        range = Text.Range.length(snapshot1.node.source)
        block <- make_node_blocks(snapshot1, List(("", range)))
      } yield block)
  }

  def find_facts_index_command(
    sessions: List[String],
    ssh: SSH.System = SSH.Local,
    isabelle_home: Path = Path.current,
    options: List[Options.Spec] = Nil,
    dirs: List[Path] = Nil,
    clean: Boolean = false,
    no_build: Boolean = false,
    verbose: Boolean = false,
  ): String = {
    ssh.bash_path(Isabelle_Tool.exe(isabelle_home)) + " find_facts_index" +
      dirs.map(dir => " -d " + ssh.bash_path(dir)).mkString +
      if_proper(clean, " -c") +
      if_proper(no_build, " -n") +
      if_proper(verbose, " -v") +
      Options.Spec.bash_strings(options, bg = true) +
      sessions.map(session => " " + session).mkString
  }

  def find_facts_index(
    options: Options,
    sessions: List[String],
    afp_root: Option[Path] = None,
    dirs: List[Path] = Nil,
    clean: Boolean = false,
    progress: Progress = new Progress
  ): Unit = {
    val store = Store(options)
    val solr = Solr.init(solr_data_dir)
    val database = options.string("find_facts_database_name")
    val session = Session(options, Resources.bootstrap)

    val selection = Sessions.Selection(sessions = sessions)
    val session_structure =
      Sessions.load_structure(options, dirs = AFP.main_dirs(afp_root) ::: dirs).selection(selection)
    val deps = Sessions.Deps.load(session_structure)
    val browser_info_context = Browser_Info.context(session_structure)

    if (sessions.isEmpty) progress.echo("Nothing to index")
    else {
      val start_date = Date.now()
      val stats =
        using(solr.init_database(database, Find_Facts.private_data, clean = clean)) { db =>
          using(Export.open_database_context(store)) { database_context =>
            val document_info = Document_Info.read(database_context, deps, sessions)

            def index_session(session_name: String): Unit = {
              using(database_context.open_session0(session_name)) { session_context =>
                val info = session_structure(session_name)
                progress.echo("Session " + info.chapter + "/" + session_name + " ...")

                Find_Facts.private_data.delete_session(db, session_name)
                deps(session_name).proper_session_theories.foreach { name =>
                  val theory_context = session_context.theory(name.theory)
                  Build.read_theory(theory_context) match {
                    case None => progress.echo_warning("No snapshot for theory " + name.theory)
                    case Some(snapshot) =>
                      progress.echo("Indexing theory " + quote(name.theory), verbose = true)
                      val blocks =
                        make_thy_blocks(options, session, browser_info_context, document_info,
                          theory_context, snapshot, info.chapter)
                      Find_Facts.private_data.update_theory(db, theory_context.theory, blocks)
                  }
                }
              }
            }

            Par_List.map(index_session, sessions)
          }

          val query = Query(Field_Filter(Field.session, sessions.map(Atom.Exact(_))))
          Find_Facts.query_stats(db, query)
        }

      val timing = Date.now() - start_date
      progress.echo("Indexed " + stats.results + " blocks with " + stats.consts + " consts, " +
        stats.typs + " typs, " + stats.thms + " thms in " + timing.message)
    }
  }


  /* Isabelle tool wrapper */

  def main_tool1(args: Array[String]): Unit = {
    Command_Line.tool {
      var afp_root: Option[Path] = None
      var clean = false
      val dirs_buffer = new mutable.ListBuffer[Path]
      var no_build = false
      var options = Options.init()
      var verbose = false

      val getopts = Getopts("""
  Usage: isabelle find_facts_index [OPTIONS] [SESSIONS ...]

    Options are:
      -A ROOT      include AFP with given root directory (":" for """ + AFP.BASE.implode + """)
      -c           clean previous index
      -d DIR       include session directory
      -n           no build -- take existing session build databases
      -o OPTION    override Isabelle system OPTION (via NAME=VAL or NAME)
      -v           verbose build

    Build and index sessions for Find_Facts.
  """,
        "A:" -> (arg => afp_root = Some(if (arg == ":") AFP.BASE else Path.explode(arg))),
        "c" -> (_ => clean = true),
        "d:" -> (arg => dirs_buffer += Path.explode(arg)),
        "n" -> (_ => no_build = true),
        "o:" -> (arg => options = options + arg),
        "v" -> (_ => verbose = true))

      val sessions = getopts(args)
      val dirs = dirs_buffer.toList

      val progress = new Console_Progress(verbose = verbose)


      /* build */

      if (!no_build) {
        def build(test: Boolean = false): Build.Results =
          Build.build(options, selection = Sessions.Selection(sessions = sessions), dirs = dirs,
            afp_root = afp_root, no_build = test, progress = if (test) new Progress else progress)

        progress.interrupt_handler {
          if (!build(test = true).ok) {
            progress.echo("Build started ...")
            val rc = build().rc
            if (rc != Process_Result.RC.ok) {
              Output.error_message("Build failed")
              sys.exit(rc)
            }
          }
        }
      }


      /* index */

      find_facts_index(options, sessions, dirs = dirs, afp_root = afp_root, clean = clean,
        progress = progress)
    }
  }


  /** index components **/

  def resolve_indexes(solr: Solr.System): Unit =
    for {
      path <- Path.split(Isabelle_System.getenv("FIND_FACTS_INDEXES"))
      database = Library.perhaps_unprefix("find_facts-", path.file_name)
      database_dir = solr.database_dir(database)
      if !database_dir.is_dir
    } Isabelle_System.copy_dir(path, database_dir, direct = true)

  def find_facts_index_build(
    database: String,
    target_dir: Path = Path.current,
    progress: Progress = new Progress
  ): Unit = {
    val solr = Solr.init(solr_data_dir)

    val component = "find_facts-" + database
    val component_dir =
      Components.Directory(target_dir + Path.basic(component)).create(progress = progress)

    Isabelle_System.copy_dir(solr.database_dir(database), component_dir.path)
    component_dir.write_settings(
      "\nFIND_FACTS_INDEXES=\"$FIND_FACTS_INDEXES:$COMPONENT/" + database + "\"")
  }


  /* Isabelle tool wrapper */

  val isabelle_tool2 = Isabelle_Tool("find_facts_index_build",
    "build Isabelle component from Find_Facts index", Scala_Project.here,
    { args =>
      var target_dir = Path.current

      val getopts = Getopts("""
  Usage: isabelle find_facts_index_build DATABASE

    Options are:
      -D DIR       target directory (default ".")

    Build Isabelle component from finalized Find_Facts index with given database name.
  """,
        "D:" -> (arg => target_dir = Path.explode(arg)))

      val more_args = getopts(args)
      val database =
        more_args match {
          case database :: Nil => database
          case _ => getopts.usage()
        }

      val progress = new Console_Progress()

      find_facts_index_build(database, target_dir = target_dir, progress = progress)
    })


  /** querying **/

  /* requests and parsing */

  case class Query_Blocks(query: Query, cursor: String)

  object Parse {
    def atom(json: JSON.T): Option[Atom] =
      JSON.string(json, "value").map(Atom.Value(_)) orElse
        JSON.string(json, "exact").map(Atom.Exact(_))

    def field(name: String): Option[Field] = Field.values.find(_.toString == name)

    def filter(json: JSON.T): Option[Filter] =
      for {
        atoms <- JSON.list(json, "either", atom)
        filter <-
          JSON.string(json, "field") match {
            case None => Some(Any_Filter(atoms))
            case Some(name) => for (field <- field(name)) yield Field_Filter(field, atoms)
          }
      } yield filter

    def select(json: JSON.T): Option[Select] =
      for {
        name <- JSON.string(json, "field")
        field <- field(name)
        values <- JSON.strings(json, "values")
      } yield Select(field, values)

    def query(json: JSON.T): Option[Query] =
      for {
        filters <- JSON.list(json, "filters", filter)
        exclude <- JSON.list(json, "exclude", filter)
        selects <- JSON.list(json, "selects", select)
      } yield Query(filters, exclude, selects)

    def query_blocks(json: JSON.T): Option[Query_Blocks] =
      for {
        query <- JSON.value(json, "query", query)
        cursor <- JSON.string(json, "cursor")
      } yield Query_Blocks(query, cursor)

    def query_block(json: JSON.T): Option[String] = for (id <- JSON.string(json, "id")) yield id
  }


  /* responses and encoding */

  case class Result(blocks: Blocks, facets: Facets)

  class Encode(options: Options) {
    val library_base_url = Url(options.string("find_facts_url_library"))
    val afp_base_url = Url(options.string("find_facts_url_afp"))

    def url(block: Block): Url = {
      val base_url = if (block.chapter == AFP.chapter) afp_base_url else library_base_url
      base_url.resolve(block.url_path.implode)
    }

    def block(block: Block): JSON.T =
      JSON.Object(
        "id" -> block.id,
        "chapter" -> block.chapter,
        "session" -> block.session,
        "theory" -> block.theory,
        "file" -> block.file,
        "file_name" -> block.file_name,
        "url" -> url(block).toString,
        "command" -> block.command,
        "start_line" -> block.start_line,
        "src_before" -> block.src_before,
        "src_after" -> block.src_after,
        "html" -> block.html,
        "entity_kname" -> block.entity_kname.orNull)

    def blocks(blocks: Blocks): JSON.T =
      JSON.Object(
        "num_found" -> blocks.num_found,
        "blocks" -> blocks.blocks.map(block),
        "cursor" -> blocks.cursor)

    def facets(facet: Facets): JSON.T =
      JSON.Object(
        "chapter" -> facet.chapter,
        "session" -> facet.session,
        "file_type" -> facet.file_type,
        "theory" -> facet.theory,
        "command" -> facet.command,
        "kinds" -> facet.kinds,
        "consts" -> facet.consts,
        "typs" -> facet.typs,
        "thms" -> facet.thms)

    def result(result: Result): JSON.T =
      JSON.Object(
        "blocks" -> blocks(result.blocks),
        "facets" -> facets(result.facets))
  }


  /* web */

  val web_sources: Path = Path.explode("$FIND_FACTS_HOME/web")
  val default_web_dir: Path = Path.explode("$FIND_FACTS_HOME_USER/web")

  def build_html(web_dir: Path = default_web_dir, progress: Progress = new Progress): String = {
    Isabelle_System.copy_dir(web_sources, web_dir, direct = true)
    val logo = Bytes.read(web_dir + Path.explode("favicon.ico"))
    val project =
      Elm.Project("Find_Facts", web_dir, head =
        List(
          HTML.style("html,body {width: 100%, height: 100%}"),
          Web_App.More_HTML.icon("data:image/x-icon;base64," + logo.encode_base64.text),
          HTML.style_file("isabelle.css"),
          HTML.style_file("https://fonts.googleapis.com/css?family=Roboto:300,400,500|Material+Icons"),
          HTML.style_file(
            "https://unpkg.com/material-components-web-elm@9.1.0/dist/material-components-web-elm.min.css"),
          HTML.script_file(
            "https://unpkg.com/material-components-web-elm@9.1.0/dist/material-components-web-elm.min.js")))
    project.build_html(progress = progress)
  }


  /* find facts */

  def find_facts_server(
    options: Options,
    port: Int = 0,
    devel: Boolean = false,
    progress: Progress = new Progress
  ): Unit = {
    val database = options.string("find_facts_database_name")
    val encode = new Encode(options)

    val isabelle_style = HTML.fonts_css("/fonts/" + _) + "\n\n" + File.read(HTML.isabelle_css)

    val html = build_html(progress = progress)

    val solr = Solr.init(solr_data_dir)
    resolve_indexes(solr)

    using(solr.open_database(database)) { db =>
      val stats = Find_Facts.query_stats(db, Query(Nil))
      progress.echo("Started Find_Facts with " + stats.results + " blocks, " +
        stats.consts + " consts, " + stats.typs + " typs, " + stats.thms + " thms")

      val server =
        HTTP.server(port, name = "", services = List(
          HTTP.Fonts_Service,
          new HTTP.Service("isabelle.css") {
            def apply(request: HTTP.Request): Option[HTTP.Response] =
              Some(HTTP.Response(Bytes(isabelle_style), "text/css"))
          },
          new HTTP.Service("find_facts") {
            def apply(request: HTTP.Request): Option[HTTP.Response] =
              Some(HTTP.Response.html(if (devel) build_html(progress = progress) else html))
          },
          new HTTP.REST_Service("api/block", progress = progress) {
            def handle(body: JSON.T): Option[JSON.T] =
              for {
                request <- Parse.query_block(body)
                block <- query_block(db, request)
              } yield encode.block(block)
          },
          new HTTP.REST_Service("api/blocks", progress = progress) {
            def handle(body: JSON.T): Option[JSON.T] =
              for (request <- Parse.query_blocks(body))
              yield encode.blocks(query_blocks(db, request.query, Some(request.cursor)))
          },
          new HTTP.REST_Service("api/query", progress = progress) {
            def handle(body: JSON.T): Option[JSON.T] =
              for (query <- Parse.query(body)) yield {
                val facet = query_facet(db, query)
                val blocks = query_blocks(db, query)
                encode.result(Result(blocks, facet))
              }
          }))

      server.start()
      progress.echo("Server started " + server.toString + "/find_facts")

      @tailrec
      def loop(): Unit = {
        Thread.sleep(Long.MaxValue)
        loop()
      }

      Isabelle_Thread.interrupt_handler(_ => server.stop()) { loop() }
    }
  }


  /* Isabelle tool wrapper */

  def main_tool3 (args: Array[String]): Unit = {
    Command_Line.tool {
      var devel = false
      var options = Options.init()
      var port = 0
      var verbose = false

      val getopts = Getopts("""
Usage: isabelle find_facts_server [OPTIONS]

  Options are:
    -d           devel mode
    -o OPTION    override Isabelle system OPTION (via NAME=VAL or NAME)
    -p PORT      explicit server port
    -v           verbose server

  Run server for Find_Facts.
""",
        "d" -> (_ => devel = true),
        "o:" -> (arg => options = options + arg),
        "p:" -> (arg => port = Value.Int.parse(arg)),
        "v" -> (_ => verbose = true))

      val more_args = getopts(args)
      if (more_args.nonEmpty) getopts.usage()

      val progress = new Console_Progress(verbose = verbose)

      find_facts_server(options, port = port, devel = devel, progress = progress)
    }
  }
}
