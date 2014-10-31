/*  Title:      Pure/Isar/outer_syntax.scala
    Author:     Makarius

Isabelle/Isar outer syntax.
*/

package isabelle


import scala.util.parsing.input.{Reader, CharSequenceReader}
import scala.collection.mutable
import scala.annotation.tailrec


object Outer_Syntax
{
  /* syntax */

  val empty: Outer_Syntax = new Outer_Syntax()

  def init(): Outer_Syntax = new Outer_Syntax(completion = Completion.init())


  /* string literals */

  def quote_string(str: String): String =
  {
    val result = new StringBuilder(str.length + 10)
    result += '"'
    for (s <- Symbol.iterator(str)) {
      if (s.length == 1) {
        val c = s(0)
        if (c < 32 && c != YXML.X && c != YXML.Y || c == '\\' || c == '"') {
          result += '\\'
          if (c < 10) result += '0'
          if (c < 100) result += '0'
          result ++= (c.asInstanceOf[Int].toString)
        }
        else result += c
      }
      else result ++= s
    }
    result += '"'
    result.toString
  }


  /* line-oriented structure */

  object Line_Structure
  {
    val init = Line_Structure()
  }

  sealed case class Line_Structure(
    improper: Boolean = true,
    command: Boolean = false,
    depth: Int = 0,
    span_depth: Int = 0,
    after_span_depth: Int = 0)


  /* overall document structure */

  sealed abstract class Document { def length: Int }
  case class Document_Block(name: String, text: String, body: List[Document]) extends Document
  {
    val length: Int = (0 /: body)(_ + _.length)
  }
  case class Document_Atom(command: Command) extends Document
  {
    def length: Int = command.length
  }
}

final class Outer_Syntax private(
  keywords: Map[String, (String, List[String])] = Map.empty,
  lexicon: Scan.Lexicon = Scan.Lexicon.empty,
  val completion: Completion = Completion.empty,
  val language_context: Completion.Language_Context = Completion.Language_Context.outer,
  val has_tokens: Boolean = true) extends Prover.Syntax
{
  /** syntax content **/

  override def toString: String =
    (for ((name, (kind, files)) <- keywords) yield {
      if (kind == Keyword.MINOR) quote(name)
      else
        quote(name) + " :: " + quote(kind) +
        (if (files.isEmpty) "" else " (" + commas_quote(files) + ")")
    }).toList.sorted.mkString("keywords\n  ", " and\n  ", "")


  /* keyword kind */

  def keyword_kind_files(name: String): Option[(String, List[String])] = keywords.get(name)
  def keyword_kind(name: String): Option[String] = keyword_kind_files(name).map(_._1)

  def is_command(name: String): Boolean =
    keyword_kind(name) match {
      case Some(kind) => kind != Keyword.MINOR
      case None => false
    }

  def command_kind(token: Token, pred: String => Boolean): Boolean =
    token.is_command && is_command(token.source) &&
      pred(keyword_kind(token.source).get)


  /* load commands */

  def load_command(name: String): Option[List[String]] =
    keywords.get(name) match {
      case Some((Keyword.THY_LOAD, exts)) => Some(exts)
      case _ => None
    }

  val load_commands: List[(String, List[String])] =
    (for ((name, (Keyword.THY_LOAD, files)) <- keywords.iterator) yield (name, files)).toList

  def load_commands_in(text: String): Boolean =
    load_commands.exists({ case (cmd, _) => text.containsSlice(cmd) })


  /* add keywords */

  def + (name: String, kind: (String, List[String]), replace: Option[String]): Outer_Syntax =
  {
    val keywords1 = keywords + (name -> kind)
    val lexicon1 = lexicon + name
    val completion1 =
      if (replace == Some("")) completion
      else completion + (name, replace getOrElse name)
    new Outer_Syntax(keywords1, lexicon1, completion1, language_context, true)
  }

  def + (name: String, kind: (String, List[String])): Outer_Syntax =
    this + (name, kind, Some(name))
  def + (name: String, kind: String): Outer_Syntax =
    this + (name, (kind, Nil), Some(name))
  def + (name: String, replace: Option[String]): Outer_Syntax =
    this + (name, (Keyword.MINOR, Nil), replace)
  def + (name: String): Outer_Syntax = this + (name, None)

  def add_keywords(keywords: Thy_Header.Keywords): Outer_Syntax =
    (this /: keywords) {
      case (syntax, (name, Some((kind, _)), replace)) =>
        syntax +
          (Symbol.decode(name), kind, replace) +
          (Symbol.encode(name), kind, replace)
      case (syntax, (name, None, replace)) =>
        syntax +
          (Symbol.decode(name), replace) +
          (Symbol.encode(name), replace)
    }


  /* language context */

  def set_language_context(context: Completion.Language_Context): Outer_Syntax =
    new Outer_Syntax(keywords, lexicon, completion, context, has_tokens)

  def no_tokens: Outer_Syntax =
  {
    require(keywords.isEmpty && lexicon.isEmpty)
    new Outer_Syntax(
      completion = completion,
      language_context = language_context,
      has_tokens = false)
  }



  /** parsing **/

  /* line-oriented structure */

  def line_structure(tokens: List[Token], struct: Outer_Syntax.Line_Structure)
    : Outer_Syntax.Line_Structure =
  {
    val improper1 = tokens.forall(_.is_improper)
    val command1 = tokens.exists(_.is_command)

    val depth1 =
      if (tokens.exists(tok => command_kind(tok, Keyword.theory))) 0
      else if (command1) struct.after_span_depth
      else struct.span_depth

    val (span_depth1, after_span_depth1) =
      ((struct.span_depth, struct.after_span_depth) /: tokens) {
        case ((x, y), tok) =>
          if (tok.is_command) {
            if (command_kind(tok, Keyword.theory_goal)) (2, 1)
            else if (command_kind(tok, Keyword.theory)) (1, 0)
            else if (command_kind(tok, Keyword.proof_goal) || tok.is_begin_block) (y + 2, y + 1)
            else if (command_kind(tok, Keyword.qed) || tok.is_end_block) (y + 1, y - 1)
            else if (command_kind(tok, Keyword.qed_global)) (1, 0)
            else (x, y)
          }
          else (x, y)
      }

    Outer_Syntax.Line_Structure(improper1, command1, depth1, span_depth1, after_span_depth1)
  }


  /* token language */

  def scan(input: CharSequence): List[Token] =
  {
    val in: Reader[Char] = new CharSequenceReader(input)
    Token.Parsers.parseAll(
        Token.Parsers.rep(Token.Parsers.token(lexicon, is_command)), in) match {
      case Token.Parsers.Success(tokens, _) => tokens
      case _ => error("Unexpected failure of tokenizing input:\n" + input.toString)
    }
  }

  def scan_line(input: CharSequence, context: Scan.Line_Context): (List[Token], Scan.Line_Context) =
  {
    var in: Reader[Char] = new CharSequenceReader(input)
    val toks = new mutable.ListBuffer[Token]
    var ctxt = context
    while (!in.atEnd) {
      Token.Parsers.parse(Token.Parsers.token_line(lexicon, is_command, ctxt), in) match {
        case Token.Parsers.Success((x, c), rest) => { toks += x; ctxt = c; in = rest }
        case Token.Parsers.NoSuccess(_, rest) =>
          error("Unexpected failure of tokenizing input:\n" + rest.source.toString)
      }
    }
    (toks.toList, ctxt)
  }


  /* command spans */

  def parse_spans(toks: List[Token]): List[Command_Span.Span] =
  {
    val result = new mutable.ListBuffer[Command_Span.Span]
    val content = new mutable.ListBuffer[Token]
    val improper = new mutable.ListBuffer[Token]

    def ship(span: List[Token])
    {
      val kind =
        if (!span.isEmpty && span.head.is_command && !span.exists(_.is_error)) {
          val name = span.head.source
          val pos = Position.Range(Text.Range(0, Symbol.iterator(name).length) + 1)
          Command_Span.Command_Span(name, pos)
        }
        else if (span.forall(_.is_improper)) Command_Span.Ignored_Span
        else Command_Span.Malformed_Span
      result += Command_Span.Span(kind, span)
    }

    def flush()
    {
      if (!content.isEmpty) { ship(content.toList); content.clear }
      if (!improper.isEmpty) { ship(improper.toList); improper.clear }
    }

    for (tok <- toks) {
      if (tok.is_command) { flush(); content += tok }
      else if (tok.is_improper) improper += tok
      else { content ++= improper; improper.clear; content += tok }
    }
    flush()

    result.toList
  }

  def parse_spans(input: CharSequence): List[Command_Span.Span] =
    parse_spans(scan(input))


  /* overall document structure */

  def heading_level(command: Command): Option[Int] =
  {
    keyword_kind(command.name) match {
      case _ if command.name == "header" => Some(0)
      case Some(Keyword.THY_HEADING1) => Some(1)
      case Some(Keyword.THY_HEADING2) | Some(Keyword.PRF_HEADING2) => Some(2)
      case Some(Keyword.THY_HEADING3) | Some(Keyword.PRF_HEADING3) => Some(3)
      case Some(Keyword.THY_HEADING4) | Some(Keyword.PRF_HEADING4) => Some(4)
      case Some(kind) if Keyword.theory(kind) => Some(5)
      case _ => None
    }
  }

  def parse_document(node_name: Document.Node.Name, text: CharSequence):
    List[Outer_Syntax.Document] =
  {
    /* stack operations */

    def buffer(): mutable.ListBuffer[Outer_Syntax.Document] =
      new mutable.ListBuffer[Outer_Syntax.Document]

    var stack: List[(Int, Command, mutable.ListBuffer[Outer_Syntax.Document])] =
      List((0, Command.empty, buffer()))

    @tailrec def close(level: Int => Boolean)
    {
      stack match {
        case (lev, command, body) :: (_, _, body2) :: rest if level(lev) =>
          body2 += Outer_Syntax.Document_Block(command.name, command.source, body.toList)
          stack = stack.tail
          close(level)
        case _ =>
      }
    }

    def result(): List[Outer_Syntax.Document] =
    {
      close(_ => true)
      stack.head._3.toList
    }

    def add(command: Command)
    {
      heading_level(command) match {
        case Some(i) =>
          close(_ > i)
          stack = (i + 1, command, buffer()) :: stack
        case None =>
      }
      stack.head._3 += Outer_Syntax.Document_Atom(command)
    }


    /* result structure */

    val spans = parse_spans(text)
    spans.foreach(span => add(Command(Document_ID.none, node_name, Nil, span)))
    result()
  }
}
