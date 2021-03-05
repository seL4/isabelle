/*  Title:      Pure/Thy/thy_header.scala
    Author:     Makarius

Static theory header information.
*/

package isabelle


import scala.util.parsing.input.Reader
import scala.util.matching.Regex


object Thy_Header
{
  /* bootstrap keywords */

  type Keywords = List[(String, Keyword.Spec)]
  type Abbrevs = List[(String, String)]

  val CHAPTER = "chapter"
  val SECTION = "section"
  val SUBSECTION = "subsection"
  val SUBSUBSECTION = "subsubsection"
  val PARAGRAPH = "paragraph"
  val SUBPARAGRAPH = "subparagraph"
  val TEXT = "text"
  val TXT = "txt"
  val TEXT_RAW = "text_raw"

  val THEORY = "theory"
  val IMPORTS = "imports"
  val KEYWORDS = "keywords"
  val ABBREVS = "abbrevs"
  val AND = "and"
  val BEGIN = "begin"

  val bootstrap_header: Keywords =
    List(
      ("%", Keyword.Spec()),
      ("(", Keyword.Spec()),
      (")", Keyword.Spec()),
      (",", Keyword.Spec()),
      ("::", Keyword.Spec()),
      ("=", Keyword.Spec()),
      (AND, Keyword.Spec()),
      (BEGIN, Keyword.Spec(kind = Keyword.QUASI_COMMAND)),
      (IMPORTS, Keyword.Spec(kind = Keyword.QUASI_COMMAND)),
      (KEYWORDS, Keyword.Spec(kind = Keyword.QUASI_COMMAND)),
      (ABBREVS, Keyword.Spec(kind = Keyword.QUASI_COMMAND)),
      (CHAPTER, Keyword.Spec(kind = Keyword.DOCUMENT_HEADING)),
      (SECTION, Keyword.Spec(kind = Keyword.DOCUMENT_HEADING)),
      (SUBSECTION, Keyword.Spec(kind = Keyword.DOCUMENT_HEADING)),
      (SUBSUBSECTION, Keyword.Spec(kind = Keyword.DOCUMENT_HEADING)),
      (PARAGRAPH, Keyword.Spec(kind = Keyword.DOCUMENT_HEADING)),
      (SUBPARAGRAPH, Keyword.Spec(kind = Keyword.DOCUMENT_HEADING)),
      (TEXT, Keyword.Spec(kind = Keyword.DOCUMENT_BODY)),
      (TXT, Keyword.Spec(kind = Keyword.DOCUMENT_BODY)),
      (TEXT_RAW, Keyword.Spec(kind = Keyword.DOCUMENT_RAW)),
      (THEORY, Keyword.Spec(kind = Keyword.THY_BEGIN, tags = List("theory"))),
      ("ML", Keyword.Spec(kind = Keyword.THY_DECL, tags = List("ML"))))

  private val bootstrap_keywords =
    Keyword.Keywords.empty.add_keywords(bootstrap_header)

  val bootstrap_syntax: Outer_Syntax =
    Outer_Syntax.empty.add_keywords(bootstrap_header)


  /* file name vs. theory name */

  val PURE = "Pure"
  val ML_BOOTSTRAP = "ML_Bootstrap"
  val ml_roots = List("ROOT0.ML" -> "ML_Root0", "ROOT.ML" -> "ML_Root")
  val bootstrap_thys = List(PURE, ML_BOOTSTRAP).map(a => a -> ("Bootstrap_" + a))

  val bootstrap_global_theories =
    (Sessions.root_name :: (ml_roots ::: bootstrap_thys).map(_._2)).map(_ -> PURE)

  private val Thy_File_Name = new Regex(""".*?([^/\\:]+)\.thy""")
  private val Split_File_Name = new Regex("""(.*?)[/\\]*([^/\\:]+)""")
  private val File_Name = new Regex(""".*?([^/\\:]+)""")

  def is_base_name(s: String): Boolean =
    s != "" && !s.exists("/\\:".contains(_))

  def split_file_name(s: String): Option[(String, String)] =
    s match {
      case Split_File_Name(s1, s2) => Some((s1, s2))
      case _ => None
    }

  def import_name(s: String): String =
    s match {
      case File_Name(name) if !name.endsWith(".thy") => name
      case _ => error("Malformed theory import: " + quote(s))
    }

  def theory_name(s: String): String =
    s match {
      case Thy_File_Name(name) => bootstrap_name(name)
      case File_Name(name) =>
        if (name == Sessions.root_name) name
        else ml_roots.collectFirst({ case (a, b) if a == name => b }).getOrElse("")
      case _ => ""
    }

  def is_ml_root(theory: String): Boolean =
    ml_roots.exists({ case (_, b) => b == theory })

  def is_bootstrap(theory: String): Boolean =
    bootstrap_thys.exists({ case (_, b) => b == theory })

  def bootstrap_name(theory: String): String =
    bootstrap_thys.collectFirst({ case (a, b) if a == theory => b }).getOrElse(theory)

  def try_read_dir(dir: Path): List[String] =
  {
    val files =
      try { File.read_dir(dir) }
      catch { case ERROR(_) => Nil }
    for { Thy_File_Name(name) <- files } yield name
  }


  /* parser */

  trait Parser extends Parse.Parser
  {
    val header: Parser[Thy_Header] =
    {
      val load_command =
        ($$$("(") ~! (position(name) <~ $$$(")")) ^^ { case _ ~ x => x }) |
          success(("", Position.none))

      val keyword_kind = atom("outer syntax keyword specification", _.is_name)
      val keyword_spec =
        position(keyword_kind) ~ load_command ~ tags ^^
          { case (a, b) ~ c ~ d =>
              Keyword.Spec(kind = a, kind_pos = b,
                load_command = c._1, load_command_pos = c._2, tags = d)
          }

      val keyword_decl =
        rep1(string) ~
        opt($$$("::") ~! keyword_spec ^^ { case _ ~ x => x }) ^^
        { case xs ~ y => xs.map((_, y.getOrElse(Keyword.Spec()))) }

      val keyword_decls =
        keyword_decl ~ rep($$$(AND) ~! keyword_decl ^^ { case _ ~ x => x }) ^^
        { case xs ~ yss => (xs :: yss).flatten }

      val abbrevs =
        rep1sep(rep1(text) ~ ($$$("=") ~! rep1(text)), $$$("and")) ^^
          { case res => for ((as ~ (_ ~ bs)) <- res; a <- as; b <- bs) yield (a, b) }

      val args =
        position(theory_name) ~
        (opt($$$(IMPORTS) ~! rep1(position(theory_name))) ^^
          { case None => Nil case Some(_ ~ xs) => xs }) ~
        (opt($$$(KEYWORDS) ~! keyword_decls) ^^
          { case None => Nil case Some(_ ~ xs) => xs }) ~
        (opt($$$(ABBREVS) ~! abbrevs) ^^
          { case None => Nil case Some(_ ~ xs) => xs }) ~
        $$$(BEGIN) ^^ { case a ~ b ~ c ~ d ~ _ => Thy_Header(a._1, a._2, b, c, d) }

      val heading =
        (command(CHAPTER) |
          command(SECTION) |
          command(SUBSECTION) |
          command(SUBSUBSECTION) |
          command(PARAGRAPH) |
          command(SUBPARAGRAPH) |
          command(TEXT) |
          command(TXT) |
          command(TEXT_RAW)) ~
        annotation ~! document_source

      (rep(heading) ~ command(THEORY) ~ annotation) ~! args ^^ { case _ ~ x => x }
    }
  }


  /* read -- lazy scanning */

  private def read_tokens(reader: Reader[Char], strict: Boolean): (List[Token], List[Token]) =
  {
    val token = Token.Parsers.token(bootstrap_keywords)
    def make_tokens(in: Reader[Char]): LazyList[Token] =
      token(in) match {
        case Token.Parsers.Success(tok, rest) => tok #:: make_tokens(rest)
        case _ => LazyList.empty
      }

    val all_tokens = make_tokens(reader)
    val drop_tokens =
      if (strict) Nil
      else all_tokens.takeWhile(tok => !tok.is_command(Thy_Header.THEORY)).toList

    val tokens = all_tokens.drop(drop_tokens.length)
    val tokens1 = tokens.takeWhile(tok => !tok.is_begin).toList
    val tokens2 = tokens.dropWhile(tok => !tok.is_begin).headOption.toList

    (drop_tokens, tokens1 ::: tokens2)
  }

  private object Parser extends Parser
  {
    def parse_header(tokens: List[Token], pos: Token.Pos): Thy_Header =
      parse(commit(header), Token.reader(tokens, pos)) match {
        case Success(result, _) => result
        case bad => error(bad.toString)
      }
  }

  def read(node_name: Document.Node.Name, reader: Reader[Char],
    command: Boolean = true,
    strict: Boolean = true): Thy_Header =
  {
    val (_, tokens0) = read_tokens(reader, true)
    val text = Scan.reader_decode_utf8(reader, Token.implode(tokens0))

    val (skip_tokens, tokens) = read_tokens(Scan.char_reader(text), strict)
    val pos =
      if (command) Token.Pos.command
      else skip_tokens.foldLeft(Token.Pos.file(node_name.node))(_ advance _)

    Parser.parse_header(tokens, pos).map(Symbol.decode).check(node_name)
  }
}

sealed case class Thy_Header(
  name: String,
  pos: Position.T,
  imports: List[(String, Position.T)],
  keywords: Thy_Header.Keywords,
  abbrevs: Thy_Header.Abbrevs)
{
  def map(f: String => String): Thy_Header =
    Thy_Header(f(name), pos,
      imports.map({ case (a, b) => (f(a), b) }),
      keywords.map({ case (a, spec) => (f(a), spec.map(f)) }),
      abbrevs.map({ case (a, b) => (f(a), f(b)) }))

  def check(node_name: Document.Node.Name): Thy_Header =
  {
    val base_name = node_name.theory_base_name
    if (Long_Name.is_qualified(name)) {
      error("Bad theory name " + quote(name) + " with qualification" + Position.here(pos))
    }
    if (base_name != name) {
      error("Bad theory name " + quote(name) + " for file " + Path.basic(base_name).thy +
        Position.here(pos) + Completion.report_theories(pos, List(base_name)))
    }

    for ((_, spec) <- keywords) {
      if (spec.kind != Keyword.THY_LOAD && spec.load_command.nonEmpty) {
        error("Illegal load command specification for kind: " + quote(spec.kind) +
          Position.here(spec.kind_pos))
      }
      if (!Command_Span.load_commands.exists(_.name == spec.load_command)) {
        val completion =
          for {
            load_command <- Command_Span.load_commands
            name = load_command.name
            if name.startsWith(spec.load_command)
          } yield (name, (Markup.LOAD_COMMAND, name))
        error("Unknown load command specification: " + quote(spec.load_command) +
          Position.here(spec.load_command_pos) +
          Completion.report_names(spec.load_command_pos, completion))
      }
    }
    this
  }
}
