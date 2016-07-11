/*  Title:      Pure/Thy/thy_header.scala
    Author:     Makarius

Static theory header information.
*/

package isabelle


import scala.annotation.tailrec
import scala.collection.mutable
import scala.util.parsing.input.{Reader, CharSequenceReader}
import scala.util.matching.Regex


object Thy_Header extends Parse.Parser
{
  /* bootstrap keywords */

  type Keywords = List[(String, Keyword.Spec, Option[String])]

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
  val AND = "and"
  val BEGIN = "begin"

  private val bootstrap_header: Keywords =
    List(
      ("%", Keyword.no_spec, None),
      ("(", Keyword.no_spec, None),
      (")", Keyword.no_spec, None),
      (",", Keyword.no_spec, None),
      ("::", Keyword.no_spec, None),
      ("==", Keyword.no_spec, None),
      (AND, Keyword.no_spec, None),
      (BEGIN, Keyword.quasi_command_spec, None),
      (IMPORTS, Keyword.quasi_command_spec, None),
      (KEYWORDS, Keyword.quasi_command_spec, None),
      (CHAPTER, (((Keyword.DOCUMENT_HEADING, Nil), Nil)), None),
      (SECTION, (((Keyword.DOCUMENT_HEADING, Nil), Nil)), None),
      (SUBSECTION, (((Keyword.DOCUMENT_HEADING, Nil), Nil)), None),
      (SUBSUBSECTION, (((Keyword.DOCUMENT_HEADING, Nil), Nil)), None),
      (PARAGRAPH, (((Keyword.DOCUMENT_HEADING, Nil), Nil)), None),
      (SUBPARAGRAPH, (((Keyword.DOCUMENT_HEADING, Nil), Nil)), None),
      (TEXT, (((Keyword.DOCUMENT_BODY, Nil), Nil)), None),
      (TXT, (((Keyword.DOCUMENT_BODY, Nil), Nil)), None),
      (TEXT_RAW, (((Keyword.DOCUMENT_RAW, Nil), Nil)), None),
      (THEORY, ((Keyword.THY_BEGIN, Nil), List("theory")), None),
      ("ML", ((Keyword.THY_DECL, Nil), List("ML")), None))

  private val bootstrap_keywords =
    Keyword.Keywords.empty.add_keywords(bootstrap_header)

  lazy val bootstrap_syntax: Outer_Syntax =
    Outer_Syntax.init().add_keywords(bootstrap_header)


  /* file name */

  val PURE = "Pure"
  val ML_BOOTSTRAP = "ML_Bootstrap"
  val ML_ROOT = "ML_Root"
  val ml_roots = List("ROOT0.ML" -> "ML_Root0", "ROOT.ML" -> ML_ROOT)
  val bootstrap_thys = List(PURE, ML_BOOTSTRAP).map(a => a -> ("Bootstrap_" + a))

  private val Base_Name = new Regex(""".*?([^/\\:]+)""")
  private val Thy_Name = new Regex(""".*?([^/\\:]+)\.thy""")

  def base_name(s: String): String =
    s match { case Base_Name(name) => name case _ => error("Malformed import: " + quote(s)) }

  def thy_name(s: String): Option[String] =
    s match { case Thy_Name(name) => Some(name) case _ => None }

  def thy_name_bootstrap(s: String): Option[String] =
    s match {
      case Thy_Name(name) =>
        Some(bootstrap_thys.collectFirst({ case (a, b) if a == name => b }).getOrElse(name))
      case Base_Name(name) => ml_roots.collectFirst({ case (a, b) if a == name => b })
      case _ => None
    }


  /* header */

  val header: Parser[Thy_Header] =
  {
    val opt_files =
      $$$("(") ~! (rep1sep(name, $$$(",")) <~ $$$(")")) ^^ { case _ ~ x => x } |
      success(Nil)

    val keyword_spec =
      atom("outer syntax keyword specification", _.is_name) ~ opt_files ~ tags ^^
      { case x ~ y ~ z => ((x, y), z) }

    val keyword_decl =
      rep1(string) ~
      opt($$$("::") ~! keyword_spec ^^ { case _ ~ x => x }) ~
      opt($$$("==") ~! name ^^ { case _ ~ x => x }) ^^
      { case xs ~ y ~ z => xs.map((_, y.getOrElse(Keyword.no_spec), z)) }

    val keyword_decls =
      keyword_decl ~ rep($$$(AND) ~! keyword_decl ^^ { case _ ~ x => x }) ^^
      { case xs ~ yss => (xs :: yss).flatten }

    val args =
      position(theory_name) ~
      (opt($$$(IMPORTS) ~! rep1(position(theory_name))) ^^
        { case None => Nil case Some(_ ~ xs) => xs }) ~
      (opt($$$(KEYWORDS) ~! keyword_decls) ^^
        { case None => Nil case Some(_ ~ xs) => xs }) ~
      $$$(BEGIN) ^^
      { case x ~ ys ~ zs ~ _ => Thy_Header(x, ys, zs) }

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
      tags ~! document_source

    (rep(heading) ~ command(THEORY) ~ tags) ~! args ^^ { case _ ~ x => x }
  }


  /* read -- lazy scanning */

  def read(reader: Reader[Char], start: Token.Pos): Thy_Header =
  {
    val token = Token.Parsers.token(bootstrap_keywords)
    val toks = new mutable.ListBuffer[Token]

    @tailrec def scan_to_begin(in: Reader[Char])
    {
      token(in) match {
        case Token.Parsers.Success(tok, rest) =>
          toks += tok
          if (!tok.is_begin) scan_to_begin(rest)
        case _ =>
      }
    }
    scan_to_begin(reader)

    parse(commit(header), Token.reader(toks.toList, start)) match {
      case Success(result, _) => result
      case bad => error(bad.toString)
    }
  }

  def read(source: CharSequence, start: Token.Pos): Thy_Header =
    read(new CharSequenceReader(source), start)
}


sealed case class Thy_Header(
  name: (String, Position.T),
  imports: List[(String, Position.T)],
  keywords: Thy_Header.Keywords)
{
  def decode_symbols: Thy_Header =
  {
    val f = Symbol.decode _
    Thy_Header((f(name._1), name._2), imports.map({ case (a, b) => (f(a), b) }),
      keywords.map({ case (a, ((x, y), z), c) =>
        (f(a), ((f(x), y.map(f)), z.map(f)), c.map(f)) }))
  }
}
