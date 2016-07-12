/*  Title:      Pure/Isar/outer_syntax.scala
    Author:     Makarius

Isabelle/Isar outer syntax.
*/

package isabelle


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
          result ++= c.asInstanceOf[Int].toString
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
  val keywords: Keyword.Keywords = Keyword.Keywords.empty,
  val completion: Completion = Completion.empty,
  val language_context: Completion.Language_Context = Completion.Language_Context.outer,
  val has_tokens: Boolean = true) extends Prover.Syntax
{
  /** syntax content **/

  override def toString: String = keywords.toString


  /* add keywords */

  def + (name: String, kind: String = "", tags: List[String] = Nil, replace: Option[String] = None)
    : Outer_Syntax =
  {
    val keywords1 = keywords + (name, kind, tags)
    val completion1 =
      if (replace == Some("")) completion
      else completion + (name, replace getOrElse name)
    new Outer_Syntax(keywords1, completion1, language_context, true)
  }

  def add_keywords(keywords: Thy_Header.Keywords): Outer_Syntax =
    (this /: keywords) {
      case (syntax, (name, ((kind, tags), _), replace)) =>
        syntax +
          (Symbol.decode(name), kind, tags, replace) +
          (Symbol.encode(name), kind, tags, replace)
    }


  /* merge */

  def ++ (other: Prover.Syntax): Prover.Syntax =
    if (this eq other) this
    else {
      val keywords1 = keywords ++ other.asInstanceOf[Outer_Syntax].keywords
      val completion1 = completion ++ other.asInstanceOf[Outer_Syntax].completion
      if ((keywords eq keywords1) && (completion eq completion1)) this
      else new Outer_Syntax(keywords1, completion1, language_context, has_tokens)
    }


  /* load commands */

  def load_command(name: String): Option[List[String]] = keywords.load_commands.get(name)
  def load_commands_in(text: String): Boolean = keywords.load_commands_in(text)


  /* language context */

  def set_language_context(context: Completion.Language_Context): Outer_Syntax =
    new Outer_Syntax(keywords, completion, context, has_tokens)

  def no_tokens: Outer_Syntax =
  {
    require(keywords.is_empty)
    new Outer_Syntax(
      completion = completion,
      language_context = language_context,
      has_tokens = false)
  }



  /** parsing **/

  /* line-oriented structure */

  def line_structure(tokens: List[Token], structure: Outer_Syntax.Line_Structure)
    : Outer_Syntax.Line_Structure =
  {
    val improper1 = tokens.forall(_.is_improper)
    val command1 = tokens.exists(_.is_command)

    val command_depth =
      tokens.iterator.filter(_.is_proper).toStream.headOption match {
        case Some(tok) =>
          if (keywords.is_command(tok, Keyword.QED_BLOCK == _))
            Some(structure.after_span_depth - 2)
          else if (keywords.is_command(tok, Keyword.PRF_CLOSE == _))
            Some(structure.after_span_depth - 1)
          else None
        case None => None
      }

    val depth1 =
      if (tokens.exists(tok =>
            keywords.is_before_command(tok) || keywords.is_command(tok, Keyword.theory))) 0
      else if (command_depth.isDefined) command_depth.get
      else if (command1) structure.after_span_depth
      else structure.span_depth

    val (span_depth1, after_span_depth1) =
      ((structure.span_depth, structure.after_span_depth) /: tokens) {
        case ((x, y), tok) =>
          if (tok.is_command) {
            if (keywords.is_command(tok, Keyword.theory_goal)) (2, 1)
            else if (keywords.is_command(tok, Keyword.theory)) (1, 0)
            else if (keywords.is_command(tok, Keyword.proof_open)) (y + 2, y + 1)
            else if (keywords.is_command(tok, Keyword.PRF_BLOCK == _)) (y + 2, y + 1)
            else if (keywords.is_command(tok, Keyword.QED_BLOCK == _)) (y - 1, y - 2)
            else if (keywords.is_command(tok, Keyword.PRF_CLOSE == _)) (y, y - 1)
            else if (keywords.is_command(tok, Keyword.proof_close)) (y + 1, y - 1)
            else if (keywords.is_command(tok, Keyword.qed_global)) (1, 0)
            else (x, y)
          }
          else (x, y)
      }

    Outer_Syntax.Line_Structure(improper1, command1, depth1, span_depth1, after_span_depth1)
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
        if (span.forall(_.is_improper)) Command_Span.Ignored_Span
        else if (span.exists(_.is_error)) Command_Span.Malformed_Span
        else
          span.find(_.is_command) match {
            case None => Command_Span.Malformed_Span
            case Some(cmd) =>
              val name = cmd.source
              val offset =
                (0 /: span.takeWhile(_ != cmd)) {
                  case (i, tok) => i + Symbol.iterator(tok.source).length }
              val end_offset = offset + Symbol.iterator(name).length
              val pos = Position.Range(Text.Range(offset, end_offset) + 1)
              Command_Span.Command_Span(name, pos)
          }
      result += Command_Span.Span(kind, span)
    }

    def flush()
    {
      if (content.nonEmpty) { ship(content.toList); content.clear }
      if (improper.nonEmpty) { ship(improper.toList); improper.clear }
    }

    for (tok <- toks) {
      if (tok.is_improper) improper += tok
      else if (keywords.is_before_command(tok) ||
        tok.is_command &&
          (!content.exists(keywords.is_before_command(_)) || content.exists(_.is_command)))
      { flush(); content += tok }
      else { content ++= improper; improper.clear; content += tok }
    }
    flush()

    result.toList
  }

  def parse_spans(input: CharSequence): List[Command_Span.Span] =
    parse_spans(Token.explode(keywords, input))


  /* overall document structure */

  def heading_level(command: Command): Option[Int] =
  {
    val name = command.span.name
    name match {
      case Thy_Header.CHAPTER => Some(0)
      case Thy_Header.SECTION => Some(1)
      case Thy_Header.SUBSECTION => Some(2)
      case Thy_Header.SUBSUBSECTION => Some(3)
      case Thy_Header.PARAGRAPH => Some(4)
      case Thy_Header.SUBPARAGRAPH => Some(5)
      case _ =>
        keywords.kinds.get(name) match {
          case Some(kind) if Keyword.theory(kind) && !Keyword.theory_end(kind) => Some(6)
          case _ => None
        }
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
          body2 += Outer_Syntax.Document_Block(command.span.name, command.source, body.toList)
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
    spans.foreach(span => add(Command(Document_ID.none, node_name, Command.no_blobs, span)))
    result()
  }
}
