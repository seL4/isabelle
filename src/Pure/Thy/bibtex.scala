/*  Title:      Pure/Thy/bibtex.scala
    Author:     Makarius

BibTeX support.
*/

package isabelle


import java.io.{File => JFile}

import scala.collection.mutable
import scala.util.parsing.combinator.RegexParsers
import scala.util.parsing.input.Reader


object Bibtex
{
  /** file format **/

  def is_bibtex(name: String): Boolean = name.endsWith(".bib")

  class File_Format extends isabelle.File_Format
  {
    val format_name: String = "bibtex"
    val file_ext: String = "bib"

    override def theory_suffix: String = "bibtex_file"
    override def theory_content(name: String): String =
      """theory "bib" imports Pure begin bibtex_file """ +
        Outer_Syntax.quote_string(name) + """ end"""

    override def html_document(snapshot: Document.Snapshot): Option[Presentation.HTML_Document] =
    {
      val name = snapshot.node_name
      if (detect(name.node)) {
        val title = "Bibliography " + quote(snapshot.node_name.path.file_name)
        val content =
          Isabelle_System.with_tmp_file("bib", "bib") { bib =>
            File.write(bib, snapshot.node.source)
            Bibtex.html_output(List(bib), style = "unsort", title = title)
          }
        Some(Presentation.HTML_Document(title, content))
      }
      else None
    }
  }



  /** bibtex errors **/

  def bibtex_errors(dir: Path, root_name: String): List[String] =
  {
    val log_path = dir + Path.explode(root_name).ext("blg")
    if (log_path.is_file) {
      val Error1 = """^(I couldn't open database file .+)$""".r
      val Error2 = """^(.+)---line (\d+) of file (.+)""".r
      Line.logical_lines(File.read(log_path)).flatMap(line =>
        line match {
          case Error1(msg) => Some("Bibtex error: " + msg)
          case Error2(msg, Value.Int(l), file) =>
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

  def check_database(database: String): (List[(String, Position.T)], List[(String, Position.T)]) =
  {
    val chunks = parse(Line.normalize(database))
    var chunk_pos = Map.empty[String, Position.T]
    val tokens = new mutable.ListBuffer[(Token, Position.T)]
    var line = 1
    var offset = 1

    def make_pos(length: Int): Position.T =
      Position.Offset(offset) ::: Position.End_Offset(offset + length) ::: Position.Line(line)

    def advance_pos(tok: Token)
    {
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

    Isabelle_System.with_tmp_dir("bibtex")(tmp_dir =>
    {
      File.write(tmp_dir + Path.explode("root.bib"),
        tokens.iterator.map(p => p._1.source).mkString("", "\n", "\n"))
      File.write(tmp_dir + Path.explode("root.aux"),
        "\\bibstyle{plain}\n\\bibdata{root}\n\\citation{*}")
      Isabelle_System.bash("\"$ISABELLE_BIBTEX\" root", cwd = tmp_dir.file)

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
                Some((false, (Word.capitalize(msg + " in entry " + quote(name)), chunk_pos(name))))
              case (Warning(msg), Warning_Line(Value.Int(l))) =>
                Some((false, (Word.capitalize(msg), get_line_pos(l))))
              case (Warning(msg), _) =>
                Some((false, (Word.capitalize(msg), Position.none)))
              case _ => None
            }
          ).partition(_._1)
        }
      (errors.map(_._2), warnings.map(_._2))
    })
  }

  object Check_Database extends Scala.Fun("bibtex_check_database")
  {
    val here = Scala_Project.here
    def apply(database: String): String =
    {
      import XML.Encode._
      YXML.string_of_body(pair(list(pair(string, properties)), list(pair(string, properties)))(
        check_database(database)))
    }
  }



  /** document model **/

  /* entries */

  def entries(text: String): List[Text.Info[String]] =
  {
    val result = new mutable.ListBuffer[Text.Info[String]]
    var offset = 0
    for (chunk <- Bibtex.parse(text)) {
      val end_offset = offset + chunk.source.length
      if (chunk.name != "" && !chunk.is_command)
        result += Text.Info(Text.Range(offset, end_offset), chunk.name)
      offset = end_offset
    }
    result.toList
  }

  def entries_iterator[A, B <: Document.Model](models: Map[A, B])
    : Iterator[Text.Info[(String, B)]] =
  {
    for {
      (_, model) <- models.iterator
      info <- model.bibtex_entries.iterator
    } yield info.map((_, model))
  }


  /* completion */

  def completion[A, B <: Document.Model](
    history: Completion.History, rendering: Rendering, caret: Text.Offset,
    models: Map[A, B]): Option[Completion.Result] =
  {
    for {
      Text.Info(r, name) <- rendering.citations(rendering.before_caret_range(caret)).headOption
      name1 <- Completion.clean_name(name)

      original <- rendering.get_text(r)
      original1 <- Completion.clean_name(Library.perhaps_unquote(original))

      entries =
        (for {
          Text.Info(_, (entry, _)) <- entries_iterator(models)
          if entry.toLowerCase.containsSlice(name1.toLowerCase) && entry != original1
        } yield entry).toList
      if entries.nonEmpty

      items =
        entries.sorted.map({
          case entry =>
            val full_name = Long_Name.qualify(Markup.CITATION, entry)
            val description = List(entry, "(BibTeX entry)")
            val replacement = quote(entry)
          Completion.Item(r, original, full_name, description, replacement, 0, false)
        }).sorted(history.ordering).take(rendering.options.int("completion_limit"))
    } yield Completion.Result(r, original, false, items)
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

  sealed case class Entry(
    kind: String,
    required: List[String],
    optional_crossref: List[String],
    optional_other: List[String])
  {
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

  val known_entries: List[Entry] =
    List(
      Entry("Article",
        List("author", "title"),
        List("journal", "year"),
        List("volume", "number", "pages", "month", "note")),
      Entry("InProceedings",
        List("author", "title"),
        List("booktitle", "year"),
        List("editor", "volume", "number", "series", "pages", "month", "address",
          "organization", "publisher", "note")),
      Entry("InCollection",
        List("author", "title", "booktitle"),
        List("publisher", "year"),
        List("editor", "volume", "number", "series", "type", "chapter", "pages",
          "edition", "month", "address", "note")),
      Entry("InBook",
        List("author", "editor", "title", "chapter"),
        List("publisher", "year"),
        List("volume", "number", "series", "type", "address", "edition", "month", "pages", "note")),
      Entry("Proceedings",
        List("title", "year"),
        List(),
        List("booktitle", "editor", "volume", "number", "series", "address", "month",
          "organization", "publisher", "note")),
      Entry("Book",
        List("author", "editor", "title"),
        List("publisher", "year"),
        List("volume", "number", "series", "address", "edition", "month", "note")),
      Entry("Booklet",
        List("title"),
        List(),
        List("author", "howpublished", "address", "month", "year", "note")),
      Entry("PhdThesis",
        List("author", "title", "school", "year"),
        List(),
        List("type", "address", "month", "note")),
      Entry("MastersThesis",
        List("author", "title", "school", "year"),
        List(),
        List("type", "address", "month", "note")),
      Entry("TechReport",
        List("author", "title", "institution", "year"),
        List(),
        List("type", "number", "address", "month", "note")),
      Entry("Manual",
        List("title"),
        List(),
        List("author", "organization", "address", "edition", "month", "year", "note")),
      Entry("Unpublished",
        List("author", "title", "note"),
        List(),
        List("month", "year")),
      Entry("Misc",
        List(),
        List(),
        List("author", "title", "howpublished", "month", "year", "note")))

  def get_entry(kind: String): Option[Entry] =
    known_entries.find(entry => entry.kind.toLowerCase == kind.toLowerCase)

  def is_entry(kind: String): Boolean = get_entry(kind).isDefined



  /** tokens and chunks **/

  object Token
  {
    object Kind extends Enumeration
    {
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

  sealed case class Token(kind: Token.Kind.Value, source: String)
  {
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

  case class Chunk(kind: String, tokens: List[Token])
  {
    val source = tokens.map(_.source).mkString

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
      else (0 /: tokens.takeWhile(tok => !tok.is_open)){ case (n, tok) => n + tok.source.length }

    def is_ignored: Boolean = kind == "" && tokens.forall(_.is_ignored)
    def is_malformed: Boolean = kind == "" || tokens.exists(_.is_malformed)
    def is_command: Boolean = Bibtex.is_command(kind) && name != "" && content.isDefined
    def is_entry: Boolean = Bibtex.is_entry(kind) && name != "" && content.isDefined
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
  val Closed = Delimited(false, 0)

  private def token(kind: Token.Kind.Value)(source: String): Token = Token(kind, source)
  private def keyword(source: String): Token = Token(Token.Kind.KEYWORD, source)


  // See also https://ctan.org/tex-archive/biblio/bibtex/base/bibtex.web
  // module @<Scan for and process a \.{.bib} command or database entry@>.

  object Parsers extends RegexParsers
  {
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
      new Parser[(String, Delimited)]
      {
        require(if (delim.quoted) delim.depth > 0 else delim.depth >= 0)

        def apply(in: Input) =
        {
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

    val other_token = "[=#,]".r ^^ keyword | (nat | (ident | space))


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
          else if (is_entry(a)) Token.Kind.ENTRY
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

    def chunk_line(ctxt: Line_Context): Parser[(Chunk, Line_Context)] =
    {
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

  def parse_line(input: CharSequence, context: Line_Context): (List[Chunk], Line_Context) =
  {
    var in: Reader[Char] = Scan.char_reader(input)
    val chunks = new mutable.ListBuffer[Chunk]
    var ctxt = context
    while (!in.atEnd) {
      Parsers.parse(Parsers.chunk_line(ctxt), in) match {
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
    chronological: Boolean = false): String =
  {
    Isabelle_System.with_tmp_dir("bibtex")(tmp_dir =>
    {
      /* database files */

      val bib_files = bib.map(_.drop_ext)
      val bib_names =
      {
        val names0 = bib_files.map(_.file_name)
        if (Library.duplicates(names0).isEmpty) names0
        else names0.zipWithIndex.map({ case (name, i) => (i + 1).toString + "-" + name })
      }

      for ((a, b) <- bib_files zip bib_names) {
        File.copy(a.ext("bib"), tmp_dir + Path.basic(b).ext("bib"))
      }


      /* style file */

      val bst =
        output_styles.toMap.get(style) match {
          case Some(base) => base + (if (chronological) "c" else "") + ".bst"
          case None =>
            error("Bad style for bibtex HTML output: " + quote(style) +
              "\n(expected: " + commas_quote(output_styles.map(_._1)) + ")")
        }
      File.copy(Path.explode("$BIB2XHTML_HOME/bst") + Path.explode(bst), tmp_dir)


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
          (if (title != "") " -h " + Bash.string(title) + " " else "") +
          " " + File.bash_path(in_file) + " " + File.bash_path(out_file),
        cwd = tmp_dir.file).check

      val html = File.read(tmp_dir + out_file)

      if (body) {
        cat_lines(
          split_lines(html).
            dropWhile(line => !line.startsWith("<!-- BEGIN BIBLIOGRAPHY")).reverse.
            dropWhile(line => !line.startsWith("<!-- END BIBLIOGRAPHY")).reverse)
      }
      else html
    })
  }
}
