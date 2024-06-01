/*  Title:      Pure/General/bibtex.scala
    Author:     Makarius

Support for BibTeX.
*/

package isabelle


import java.io.{File => JFile}

import scala.collection.mutable
import scala.util.parsing.combinator.RegexParsers
import scala.util.parsing.input.Reader
import scala.util.matching.Regex

import isabelle.{Token => Isar_Token}


object Bibtex {
  /** file format **/

  class File_Format extends isabelle.File_Format {
    val format_name: String = "bibtex"
    val file_ext: String = "bib"

    override def parse_data(name: String, text: String): Bibtex.Entries =
      Bibtex.Entries.parse(text, Isar_Token.Pos.file(name))

    override def theory_suffix: String = "bibtex_file"
    override def theory_content(name: String): String =
      """theory "bib" imports Pure begin bibtex_file "." end"""
    override def theory_excluded(name: String): Boolean = name == "bib"

    override def html_document(snapshot: Document.Snapshot): Option[Browser_Info.HTML_Document] = {
      val name = snapshot.node_name
      if (detect(name.node)) {
        val title = "Bibliography " + quote(snapshot.node_name.file_name)
        val content =
          Isabelle_System.with_tmp_file("bib", "bib") { bib =>
            File.write(bib, snapshot.node.source)
            Bibtex.html_output(List(bib), style = "unsort", title = title)
          }
        Some(Browser_Info.HTML_Document(title, content))
      }
      else None
    }
  }



  /** bibtex errors **/

  def bibtex_errors(dir: Path, root_name: String): List[String] = {
    val log_path = dir + Path.explode(root_name).blg
    if (log_path.is_file) {
      val Error1 = """^(I couldn't open database file .+)$""".r
      val Error2 = """^(I found no .+)$""".r
      val Error3 = """^(.+)---line (\d+) of file (.+)""".r
      Line.logical_lines(File.read(log_path)).flatMap(line =>
        line match {
          case Error1(msg) => Some("Bibtex error: " + msg)
          case Error2(msg) => Some("Bibtex error: " + msg)
          case Error3(msg, Value.Int(l), file) =>
            val path = File.standard_path(file)
            if (Path.is_wellformed(path)) {
              val pos = Position.Line_File(l, (dir + Path.explode(path)).canonical.implode)
              Some("Bibtex error" + Position.here(pos) + ":\n  " + msg)
            }
            else None
          case _ => None
        })
    }
    else Nil
  }



  /** check database **/

  def check_database(database: String): (List[(String, Position.T)], List[(String, Position.T)]) = {
    val chunks = parse(Line.normalize(database))
    var chunk_pos = Map.empty[String, Position.T]
    val tokens = new mutable.ListBuffer[(Token, Position.T)]
    var line = 1
    var offset = 1

    def make_pos(length: Int): Position.T =
      Position.Offset(offset) ::: Position.End_Offset(offset + length) ::: Position.Line(line)

    def advance_pos(tok: Token): Unit = {
      for (s <- Symbol.iterator(tok.source)) {
        if (Symbol.is_newline(s)) line += 1
        offset += 1
      }
    }

    def get_line_pos(l: Int): Position.T =
      if (0 < l && l <= tokens.length) tokens(l - 1)._2 else Position.none

    for (chunk <- chunks) {
      val name = chunk.name
      if (name != "" && !chunk_pos.isDefinedAt(name)) {
        chunk_pos += (name -> make_pos(chunk.heading_length))
      }
      for (tok <- chunk.tokens) {
        tokens += (tok.copy(source = tok.source.replace("\n", " ")) -> make_pos(tok.source.length))
        advance_pos(tok)
      }
    }

    Isabelle_System.with_tmp_dir("bibtex") { tmp_dir =>
      File.write(tmp_dir + Path.explode("root.bib"),
        tokens.iterator.map(p => p._1.source).mkString("", "\n", "\n"))
      File.write(tmp_dir + Path.explode("root.aux"),
        "\\bibstyle{plain}\n\\bibdata{root}\n\\citation{*}")
      Isabelle_System.bash("\"$ISABELLE_BIBTEX\" root", cwd = tmp_dir)

      val Error = """^(.*)---line (\d+) of file root.bib$""".r
      val Warning = """^Warning--(.+)$""".r
      val Warning_Line = """--line (\d+) of file root.bib$""".r
      val Warning_in_Chunk = """^Warning--(.+) in (.+)$""".r

      val log_file = tmp_dir + Path.explode("root.blg")
      val lines = if (log_file.is_file) Line.logical_lines(File.read(log_file)) else Nil

      val (errors, warnings) =
        if (lines.isEmpty) (Nil, Nil)
        else {
          lines.zip(lines.tail ::: List("")).flatMap(
            {
              case (Error(msg, Value.Int(l)), _) =>
                Some((true, (msg, get_line_pos(l))))
              case (Warning_in_Chunk(msg, name), _) if chunk_pos.isDefinedAt(name) =>
                Some((false, (Word.capitalized(msg) + " in entry " + quote(name), chunk_pos(name))))
              case (Warning(msg), Warning_Line(Value.Int(l))) =>
                Some((false, (Word.capitalized(msg), get_line_pos(l))))
              case (Warning(msg), _) =>
                Some((false, (Word.capitalized(msg), Position.none)))
              case _ => None
            }
          ).partition(_._1)
        }
      (errors.map(_._2), warnings.map(_._2))
    }
  }

  object Check_Database extends Scala.Fun_String("bibtex_check_database") {
    val here = Scala_Project.here
    def apply(database: String): String = {
      import XML.Encode._
      YXML.string_of_body(pair(list(pair(string, properties)), list(pair(string, properties)))(
        check_database(database)))
    }
  }



  /** document model **/

  /* entries */

  sealed case class Entry(name: String, pos: Position.T) {
    def encode: String = YXML.string_of_body(XML.Encode.properties(Markup.Name(name) ::: pos))
  }

  object Entries {
    val empty: Entries = apply(Nil)

    def apply(entries: List[Entry], errors: List[String] = Nil): Entries =
      new Entries(entries, errors)

    def parse(text: String, start: Isar_Token.Pos = Isar_Token.Pos.start): Entries = {
      val entries = new mutable.ListBuffer[Entry]
      var pos = start
      var err_line = 0

      try {
        for (chunk <- Bibtex.parse(text)) {
          val pos1 = pos.advance(chunk.source)
          if (chunk.name != "" && !chunk.is_command) {
            entries += Entry(chunk.name, pos.position(pos1.offset))
          }
          if (chunk.is_malformed && err_line == 0) { err_line = pos.line }
          pos = pos1
        }

        val err_pos =
          if (err_line == 0 || pos.file.isEmpty) Position.none
          else Position.Line_File(err_line, pos.file)
        val errors =
          if (err_line == 0) Nil
          else List("Malformed bibtex file" + Position.here(err_pos))

        apply(entries.toList, errors = errors)
      }
      catch { case ERROR(msg) => apply(Nil, errors = List(msg)) }
    }
  }

  final class Entries private(val entries: List[Entry], val errors: List[String]) {
    override def toString: String = "Bibtex.Entries(" + entries.length + ")"

    def ::: (other: Entries): Entries =
      new Entries(other.entries ::: entries, other.errors ::: errors)
  }

  object Session_Entries extends Scala.Fun("bibtex_session_entries") {
    val here = Scala_Project.here

    override def invoke(session: Session, args: List[Bytes]): List[Bytes] = {
      val sessions = session.resources.sessions_structure
      val id = Value.Long.parse(Library.the_single(args).text)
      val qualifier =
        session.get_state().lookup_id(id) match {
          case None => Sessions.DRAFT
          case Some(st) => sessions.theory_qualifier(st.command.node_name.theory)
        }
      val res =
        if (qualifier == Sessions.DRAFT || !sessions.defined(qualifier)) Nil
        else qualifier :: sessions(qualifier).bibtex_entries.entries.map(_.encode)
      res.map(Bytes.apply)
    }
  }



  /** content **/

  private val months = List(
    "jan",
    "feb",
    "mar",
    "apr",
    "may",
    "jun",
    "jul",
    "aug",
    "sep",
    "oct",
    "nov",
    "dec")
  def is_month(s: String): Boolean = months.contains(s.toLowerCase)

  private val commands = List("preamble", "string")
  def is_command(s: String): Boolean = commands.contains(s.toLowerCase)

  sealed case class Entry_Type(
    kind: String,
    required: List[String],
    optional_crossref: List[String],
    optional_other: List[String]
  ) {
    val optional_standard: List[String] = List("url", "doi", "ee")

    def is_required(s: String): Boolean = required.contains(s.toLowerCase)
    def is_optional(s: String): Boolean =
      optional_crossref.contains(s.toLowerCase) ||
      optional_other.contains(s.toLowerCase) ||
      optional_standard.contains(s.toLowerCase)

    def fields: List[String] =
      required ::: optional_crossref ::: optional_other ::: optional_standard

    def template: String =
      "@" + kind + "{,\n" + fields.map(x => "  " + x + " = {},\n").mkString + "}\n"
  }

  val known_entries: List[Entry_Type] =
    List(
      Entry_Type("Article",
        List("author", "title"),
        List("journal", "year"),
        List("volume", "number", "pages", "month", "note")),
      Entry_Type("InProceedings",
        List("author", "title"),
        List("booktitle", "year"),
        List("editor", "volume", "number", "series", "pages", "month", "address",
          "organization", "publisher", "note")),
      Entry_Type("InCollection",
        List("author", "title", "booktitle"),
        List("publisher", "year"),
        List("editor", "volume", "number", "series", "type", "chapter", "pages",
          "edition", "month", "address", "note")),
      Entry_Type("InBook",
        List("author", "editor", "title", "chapter"),
        List("publisher", "year"),
        List("volume", "number", "series", "type", "address", "edition", "month", "pages", "note")),
      Entry_Type("Proceedings",
        List("title", "year"),
        List(),
        List("booktitle", "editor", "volume", "number", "series", "address", "month",
          "organization", "publisher", "note")),
      Entry_Type("Book",
        List("author", "editor", "title"),
        List("publisher", "year"),
        List("volume", "number", "series", "address", "edition", "month", "note")),
      Entry_Type("Booklet",
        List("title"),
        List(),
        List("author", "howpublished", "address", "month", "year", "note")),
      Entry_Type("PhdThesis",
        List("author", "title", "school", "year"),
        List(),
        List("type", "address", "month", "note")),
      Entry_Type("MastersThesis",
        List("author", "title", "school", "year"),
        List(),
        List("type", "address", "month", "note")),
      Entry_Type("TechReport",
        List("author", "title", "institution", "year"),
        List(),
        List("type", "number", "address", "month", "note")),
      Entry_Type("Manual",
        List("title"),
        List(),
        List("author", "organization", "address", "edition", "month", "year", "note")),
      Entry_Type("Unpublished",
        List("author", "title", "note"),
        List(),
        List("month", "year")),
      Entry_Type("Misc",
        List(),
        List(),
        List("author", "title", "howpublished", "month", "year", "note")))

  def known_entry(kind: String): Option[Entry_Type] =
    known_entries.find(entry => entry.kind.toLowerCase == kind.toLowerCase)



  /** tokens and chunks **/

  object Token {
    object Kind extends Enumeration {
      val COMMAND = Value("command")
      val ENTRY = Value("entry")
      val KEYWORD = Value("keyword")
      val NAT = Value("natural number")
      val STRING = Value("string")
      val NAME = Value("name")
      val IDENT = Value("identifier")
      val SPACE = Value("white space")
      val COMMENT = Value("ignored text")
      val ERROR = Value("bad input")
    }
  }

  sealed case class Token(kind: Token.Kind.Value, source: String) {
    def is_kind: Boolean =
      kind == Token.Kind.COMMAND ||
      kind == Token.Kind.ENTRY ||
      kind == Token.Kind.IDENT
    def is_name: Boolean =
      kind == Token.Kind.NAME ||
      kind == Token.Kind.IDENT
    def is_ignored: Boolean =
      kind == Token.Kind.SPACE ||
      kind == Token.Kind.COMMENT
    def is_malformed: Boolean =
      kind == Token.Kind.ERROR
    def is_open: Boolean =
      kind == Token.Kind.KEYWORD && (source == "{" || source == "(")
  }

  case class Chunk(kind: String, tokens: List[Token]) {
    val source: String = tokens.map(_.source).mkString

    private val content: Option[List[Token]] =
      tokens match {
        case Token(Token.Kind.KEYWORD, "@") :: body if body.nonEmpty =>
          (body.init.filterNot(_.is_ignored), body.last) match {
            case (tok :: Token(Token.Kind.KEYWORD, "{") :: toks, Token(Token.Kind.KEYWORD, "}"))
            if tok.is_kind => Some(toks)

            case (tok :: Token(Token.Kind.KEYWORD, "(") :: toks, Token(Token.Kind.KEYWORD, ")"))
            if tok.is_kind => Some(toks)

            case _ => None
          }
        case _ => None
      }

    def name: String =
      content match {
        case Some(tok :: _) if tok.is_name => tok.source
        case _ => ""
      }

    def heading_length: Int =
      if (name == "") 1
      else {
        tokens.takeWhile(tok => !tok.is_open).foldLeft(0) { case (n, tok) => n + tok.source.length }
      }

    def is_ignored: Boolean = kind == "" && tokens.forall(_.is_ignored)
    def is_malformed: Boolean = tokens.exists(_.is_malformed)
    def is_command: Boolean = Bibtex.is_command(kind) && name != "" && content.isDefined
    def is_entry: Boolean = Bibtex.known_entry(kind).isDefined && name != "" && content.isDefined
  }



  /** parsing **/

  // context of partial line-oriented scans
  abstract class Line_Context
  case object Ignored extends Line_Context
  case object At extends Line_Context
  case class Item_Start(kind: String) extends Line_Context
  case class Item_Open(kind: String, end: String) extends Line_Context
  case class Item(kind: String, end: String, delim: Delimited) extends Line_Context

  case class Delimited(quoted: Boolean, depth: Int)
  val Closed: Delimited = Delimited(false, 0)

  private def token(kind: Token.Kind.Value)(source: String): Token = Token(kind, source)
  private def keyword(source: String): Token = Token(Token.Kind.KEYWORD, source)


  // See also https://ctan.org/tex-archive/biblio/bibtex/base/bibtex.web
  // module @<Scan for and process a \.{.bib} command or database entry@>.

  object Parsers extends RegexParsers {
    /* white space and comments */

    override val whiteSpace = "".r

    private val space = """[ \t\n\r]+""".r ^^ token(Token.Kind.SPACE)
    private val spaces = rep(space)


    /* ignored text */

    private val ignored: Parser[Chunk] =
      rep1("""(?i)([^@]+|@[ \t]*comment)""".r) ^^ {
        case ss => Chunk("", List(Token(Token.Kind.COMMENT, ss.mkString))) }

    private def ignored_line: Parser[(Chunk, Line_Context)] =
      ignored ^^ { case a => (a, Ignored) }


    /* delimited string: outermost "..." or {...} and body with balanced {...} */

    // see also bibtex.web: scan_a_field_token_and_eat_white, scan_balanced_braces
    private def delimited_depth(delim: Delimited): Parser[(String, Delimited)] =
      new Parser[(String, Delimited)] {
        require(if (delim.quoted) delim.depth > 0 else delim.depth >= 0,
          "bad delimiter depth")

        def apply(in: Input): ParseResult[(String, Delimited)] = {
          val start = in.offset
          val end = in.source.length

          var i = start
          var q = delim.quoted
          var d = delim.depth
          var finished = false
          while (!finished && i < end) {
            val c = in.source.charAt(i)

            if (c == '"' && d == 0) { i += 1; d = 1; q = true }
            else if (c == '"' && d == 1 && q) {
              i += 1; d = 0; q = false; finished = true
            }
            else if (c == '{') { i += 1; d += 1 }
            else if (c == '}') {
              if (d == 1 && !q || d > 1) { i += 1; d -= 1; if (d == 0) finished = true }
              else {i = start; finished = true }
            }
            else if (d > 0) i += 1
            else finished = true
          }
          if (i == start) Failure("bad input", in)
          else {
            val s = in.source.subSequence(start, i).toString
            Success((s, Delimited(q, d)), in.drop(i - start))
          }
        }
      }.named("delimited_depth")

    private def delimited: Parser[Token] =
      delimited_depth(Closed) ^?
        { case (s, delim) if delim == Closed => Token(Token.Kind.STRING, s) }

    private def recover_delimited: Parser[Token] =
      """["{][^@]*""".r ^^ token(Token.Kind.ERROR)

    def delimited_line(ctxt: Item): Parser[(Chunk, Line_Context)] =
      delimited_depth(ctxt.delim) ^^ { case (s, delim1) =>
        (Chunk(ctxt.kind, List(Token(Token.Kind.STRING, s))), ctxt.copy(delim = delim1)) } |
      recover_delimited ^^ { case a => (Chunk(ctxt.kind, List(a)), Ignored) }


    /* other tokens */

    private val at = "@" ^^ keyword

    private val nat = "[0-9]+".r ^^ token(Token.Kind.NAT)

    private val name = """[\x21-\x7f&&[^"#%'(),={}]]+""".r ^^ token(Token.Kind.NAME)

    private val identifier =
      """[\x21-\x7f&&[^"#%'(),={}0-9]][\x21-\x7f&&[^"#%'(),={}]]*""".r

    private val ident = identifier ^^ token(Token.Kind.IDENT)

    val other_token: Parser[Token] = "[=#,]".r ^^ keyword | (nat | (ident | space))


    /* body */

    private val body =
      delimited | (recover_delimited | other_token)

    private def body_line(ctxt: Item) =
      if (ctxt.delim.depth > 0)
        delimited_line(ctxt)
      else
        delimited_line(ctxt) |
        other_token ^^ { case a => (Chunk(ctxt.kind, List(a)), ctxt) } |
        ctxt.end ^^ { case a => (Chunk(ctxt.kind, List(keyword(a))), Ignored) }


    /* items: command or entry */

    private val item_kind =
      identifier ^^ { case a =>
        val kind =
          if (is_command(a)) Token.Kind.COMMAND
          else if (known_entry(a).isDefined) Token.Kind.ENTRY
          else Token.Kind.IDENT
        Token(kind, a)
      }

    private val item_begin =
      "{" ^^ { case a => ("}", keyword(a)) } |
      "(" ^^ { case a => (")", keyword(a)) }

    private def item_name(kind: String) =
      kind.toLowerCase match {
        case "preamble" => failure("")
        case "string" => identifier ^^ token(Token.Kind.NAME)
        case _ => name
      }

    private val item_start =
      at ~ spaces ~ item_kind ~ spaces ^^
        { case a ~ b ~ c ~ d => (c.source, List(a) ::: b ::: List(c) ::: d) }

    private val item: Parser[Chunk] =
      (item_start ~ item_begin ~ spaces) into
        { case (kind, a) ~ ((end, b)) ~ c =>
            opt(item_name(kind)) ~ rep(body) ~ opt(end ^^ keyword) ^^ {
              case d ~ e ~ f => Chunk(kind, a ::: List(b) ::: c ::: d.toList ::: e ::: f.toList) } }

    private val recover_item: Parser[Chunk] =
      at ~ "[^@]*".r ^^ { case a ~ b => Chunk("", List(a, Token(Token.Kind.ERROR, b))) }


    /* chunks */

    val chunk: Parser[Chunk] = ignored | (item | recover_item)

    def chunk_line(ctxt: Line_Context): Parser[(Chunk, Line_Context)] = {
      ctxt match {
        case Ignored =>
          ignored_line |
          at ^^ { case a => (Chunk("", List(a)), At) }

        case At =>
          space ^^ { case a => (Chunk("", List(a)), ctxt) } |
          item_kind ^^ { case a => (Chunk(a.source, List(a)), Item_Start(a.source)) } |
          recover_item ^^ { case a => (a, Ignored) } |
          ignored_line

        case Item_Start(kind) =>
          space ^^ { case a => (Chunk(kind, List(a)), ctxt) } |
          item_begin ^^ { case (end, a) => (Chunk(kind, List(a)), Item_Open(kind, end)) } |
          recover_item ^^ { case a => (a, Ignored) } |
          ignored_line

        case Item_Open(kind, end) =>
          space ^^ { case a => (Chunk(kind, List(a)), ctxt) } |
          item_name(kind) ^^ { case a => (Chunk(kind, List(a)), Item(kind, end, Closed)) } |
          body_line(Item(kind, end, Closed)) |
          ignored_line

        case item_ctxt: Item =>
          body_line(item_ctxt) |
          ignored_line

        case _ => failure("")
      }
    }
  }


  /* parse */

  def parse(input: CharSequence): List[Chunk] =
    Parsers.parseAll(Parsers.rep(Parsers.chunk), Scan.char_reader(input)) match {
      case Parsers.Success(result, _) => result
      case _ => error("Unexpected failure to parse input:\n" + input.toString)
    }

  def parse_line(input: CharSequence, context: Line_Context): (List[Chunk], Line_Context) = {
    var in: Reader[Char] = Scan.char_reader(input)
    val chunks = new mutable.ListBuffer[Chunk]
    var ctxt = context
    while (!in.atEnd) {
      val result = Parsers.parse(Parsers.chunk_line(ctxt), in)
      (result : @unchecked) match {
        case Parsers.Success((x, c), rest) => chunks += x; ctxt = c; in = rest
        case Parsers.NoSuccess(_, rest) =>
          error("Unepected failure to parse input:\n" + rest.source.toString)
      }
    }
    (chunks.toList, ctxt)
  }



  /** HTML output **/

  private val output_styles =
    List(
      "" -> "html-n",
      "plain" -> "html-n",
      "alpha" -> "html-a",
      "named" -> "html-n",
      "paragraph" -> "html-n",
      "unsort" -> "html-u",
      "unsortlist" -> "html-u")

  def html_output(bib: List[Path],
    title: String = "Bibliography",
    body: Boolean = false,
    citations: List[String] = List("*"),
    style: String = "",
    chronological: Boolean = false
  ): String = {
    Isabelle_System.with_tmp_dir("bibtex") { tmp_dir =>
      /* database files */

      val bib_files = bib.map(_.drop_ext)
      val bib_names = {
        val names0 = bib_files.map(_.file_name)
        if (Library.duplicates(names0).isEmpty) names0
        else names0.zipWithIndex.map({ case (name, i) => (i + 1).toString + "-" + name })
      }

      for ((a, b) <- bib_files zip bib_names) {
        Isabelle_System.copy_file(a.bib, tmp_dir + Path.basic(b).bib)
      }


      /* style file */

      val bst =
        output_styles.toMap.get(style) match {
          case Some(base) => base + (if (chronological) "c" else "") + ".bst"
          case None =>
            error("Bad style for bibtex HTML output: " + quote(style) +
              "\n(expected: " + commas_quote(output_styles.map(_._1)) + ")")
        }
      Isabelle_System.copy_file(Path.explode("$BIB2XHTML_HOME/bst") + Path.explode(bst), tmp_dir)


      /* result */

      val in_file = Path.explode("bib.aux")
      val out_file = Path.explode("bib.html")

      File.write(tmp_dir + in_file,
        bib_names.mkString("\\bibdata{", ",", "}\n") +
        citations.map(cite => "\\citation{" + cite + "}\n").mkString)

      Isabelle_System.bash(
        "\"$BIB2XHTML_HOME/main/bib2xhtml.pl\" -B \"$ISABELLE_BIBTEX\"" +
          " -u -s " + Bash.string(proper_string(style) getOrElse "empty") +
          (if (chronological) " -c" else "") +
          if_proper(title, " -h " + Bash.string(title) + " ") +
          " " + File.bash_path(in_file) + " " + File.bash_path(out_file),
        cwd = tmp_dir).check

      val html = File.read(tmp_dir + out_file)

      if (body) {
        cat_lines(
          split_lines(html).
            dropWhile(line => !line.startsWith("<!-- BEGIN BIBLIOGRAPHY")).reverse.
            dropWhile(line => !line.startsWith("<!-- END BIBLIOGRAPHY")).reverse)
      }
      else html
    }
  }



  /** cite commands and antiquotations **/

  /* cite commands */

  def cite_commands(options: Options): List[String] =
    space_explode(',', options.string("document_cite_commands"))

  val CITE = "cite"
  val NOCITE = "nocite"


  /* citations within theory source */

  object Cite {
    def unapply(tree: XML.Tree): Option[Inner] =
      tree match {
        case XML.Elem(Markup(Markup.Latex_Cite.name, props), body) =>
          val kind = Markup.Kind.unapply(props).getOrElse(CITE)
          val citations = Markup.Citations.get(props)
          val pos = props.filter(Markup.position_property)
          Some(Inner(kind, citations, body, pos))
        case _ => None
      }

    sealed case class Inner(kind: String, citations: String, location: XML.Body, pos: Position.T) {
      def nocite: Inner = copy(kind = NOCITE, location = Nil)

      def latex_text: Latex.Text = {
        val props =
          (if (kind.nonEmpty) Markup.Kind(kind) else Nil) :::
          Markup.Citations(citations) ::: pos
        List(XML.Elem(Markup.Latex_Cite(props), location))
      }

      override def toString: String = citations
    }

    sealed case class Outer(kind: String, body: String, start: Isar_Token.Pos) {
      def pos: Position.T = start.position()

      def parse: Option[Inner] = {
        val tokens = Isar_Token.explode(Parsers.keywords, body)
        Parsers.parse_all(Parsers.inner(pos), Isar_Token.reader(tokens, start)) match {
          case Parsers.Success(res, _) => Some(res)
          case _ => None
        }
      }

      def errors: List[String] =
        if (parse.isDefined) Nil
        else List("Malformed citation" + Position.here(pos))

      override def toString: String =
        parse match {
          case Some(inner) => inner.toString
          case None => "<malformed>"
        }
    }

    object Parsers extends Parse.Parsers {
      val keywords: Keyword.Keywords = Thy_Header.bootstrap_keywords + "in" + "using"

      val location: Parser[String] = embedded ~ $$$("in") ^^ { case x ~ _ => x } | success("")
      val citations: Parser[String] = rep1sep(name, $$$("and")) ^^ (x => x.mkString(","))
      val kind: Parser[String] = $$$("using") ~! name ^^ { case _ ~ x => x } | success(CITE)

      def inner(pos: Position.T): Parser[Inner] =
        location ~ citations ~ kind ^^
          { case x ~ y ~ z => Inner(z, y, XML.string(x), pos) }
    }

    def parse(
      cite_commands: List[String],
      text: String,
      start: Isar_Token.Pos = Isar_Token.Pos.start
    ): List[Outer] = {
      val controls = cite_commands.map(s => Symbol.control_prefix + s + Symbol.control_suffix)
      val special = (controls ::: controls.map(Symbol.decode)).toSet

      val Parsers = Antiquote.Parsers
      Parsers.parseAll(Parsers.rep(Parsers.antiquote_special(special)), text) match {
        case Parsers.Success(ants, _) =>
          var pos = start
          val result = new mutable.ListBuffer[Outer]
          for (ant <- ants) {
            ant match {
              case Antiquote.Control(source) =>
                for {
                  head <- Symbol.iterator(source).nextOption
                  kind <- Symbol.control_name(Symbol.encode(head))
                } {
                  val rest = source.substring(head.length)
                  val (body, pos1) =
                    if (rest.isEmpty) (rest, pos)
                    else (Scan.Parsers.cartouche_content(rest), pos.advance(Symbol.open))
                  result += Outer(kind, body, pos1)
                }
              case _ =>
            }
            pos = pos.advance(ant.source)
          }
          result.toList
        case _ => error("Unexpected failure parsing special antiquotations:\n" + text)
      }
    }
  }


  /* update old forms: @{cite ...} and \cite{...} */

  def cite_antiquotation(name: String, body: String): String =
    """\<^""" + name + """>\<open>""" + body + """\<close>"""

  def cite_antiquotation(name: String, location: String, citations: List[String]): String = {
    val body =
      if_proper(location, Symbol.cartouche(location) + " in ") +
      citations.map(quote).mkString(" and ")
    cite_antiquotation(name, body)
  }

  private val Cite_Command = """\\(cite|nocite|citet|citep)((?:\[[^\]]*\])?)\{([^}]*)\}""".r
  private val Cite_Macro = """\[\s*cite_macro\s*=\s*"?(\w+)"?\]\s*""".r

  def update_cite_commands(str: String): String =
    Cite_Command.replaceAllIn(str, { m =>
      val name = m.group(1)
      val loc = m.group(2)
      val location =
        if (loc.startsWith("[") && loc.endsWith("]")) loc.substring(1, loc.length - 1)
        else loc
      val citations = space_explode(',', m.group(3)).map(_.trim)
      Regex.quoteReplacement(cite_antiquotation(name, location, citations))
    })

  def update_cite_antiquotation(cite_commands: List[String], str: String): String = {
    val opt_body =
      for {
        str1 <- Library.try_unprefix("@{cite", str)
        str2 <- Library.try_unsuffix("}", str1)
      } yield str2.trim

    opt_body match {
      case None => str
      case Some(body0) =>
        val (name, body1) =
          Cite_Macro.findFirstMatchIn(body0) match {
            case None => (CITE, body0)
            case Some(m) => (m.group(1), Cite_Macro.replaceAllIn(body0, ""))
          }
        val body2 = body1.replace("""\<close>""", """\<close> in""")
        if (cite_commands.contains(name)) cite_antiquotation(name, body2)
        else cite_antiquotation(CITE, body2 + " using " + quote(name))
    }
  }
}
