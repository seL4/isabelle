/*  Title:      Tools/jEdit/src/token_markup.scala
    Author:     Makarius

Outer syntax token markup.
*/

package isabelle.jedit


import isabelle._

import javax.swing.text.Segment

import org.gjt.sp.jedit.{Mode, Buffer}
import org.gjt.sp.jedit.syntax.{Token => JEditToken, TokenMarker, TokenHandler, DummyTokenHandler,
  ParserRuleSet, ModeProvider, XModeHandler}
import org.gjt.sp.jedit.indent.IndentRule
import org.gjt.sp.jedit.buffer.JEditBuffer


object Token_Markup
{
  /* line context */

  object Line_Context
  {
    def init(mode: String): Line_Context =
      new Line_Context(mode, Some(Scan.Finished), Line_Structure.init)

    def before(buffer: JEditBuffer, line: Int): Line_Context =
      if (line == 0) init(JEdit_Lib.buffer_mode(buffer))
      else after(buffer, line - 1)

    def after(buffer: JEditBuffer, line: Int): Line_Context =
    {
      val line_mgr = JEdit_Lib.buffer_line_manager(buffer)
      def context =
        line_mgr.getLineContext(line) match {
          case c: Line_Context => Some(c)
          case _ => None
        }
      context getOrElse {
        buffer.markTokens(line, DummyTokenHandler.INSTANCE)
        context getOrElse init(JEdit_Lib.buffer_mode(buffer))
      }
    }
  }

  class Line_Context(
      val mode: String,
      val context: Option[Scan.Line_Context],
      val structure: Line_Structure)
    extends TokenMarker.LineContext(new ParserRuleSet(mode, "MAIN"), null)
  {
    def get_context: Scan.Line_Context = context.getOrElse(Scan.Finished)

    override def hashCode: Int = (mode, context, structure).hashCode
    override def equals(that: Any): Boolean =
      that match {
        case other: Line_Context =>
          mode == other.mode && context == other.context && structure == other.structure
        case _ => false
      }
  }


  /* tokens from line (inclusive) */

  private def try_line_tokens(syntax: Outer_Syntax, buffer: JEditBuffer, line: Int)
    : Option[List[Token]] =
  {
    val line_context = Line_Context.before(buffer, line)
    for {
      ctxt <- line_context.context
      text <- JEdit_Lib.get_text(buffer, JEdit_Lib.line_range(buffer, line))
    } yield Token.explode_line(syntax.keywords, text, ctxt)._1
  }

  def line_token_iterator(
      syntax: Outer_Syntax,
      buffer: JEditBuffer,
      start_line: Int,
      end_line: Int): Iterator[Text.Info[Token]] =
    for {
      line <- Range(start_line max 0, end_line min buffer.getLineCount).iterator
      tokens <- try_line_tokens(syntax, buffer, line).iterator
      starts =
        tokens.iterator.scanLeft(buffer.getLineStartOffset(line))(
          (i, tok) => i + tok.source.length)
      (i, tok) <- starts zip tokens.iterator
    } yield Text.Info(Text.Range(i, i + tok.source.length), tok)

  def line_token_reverse_iterator(
      syntax: Outer_Syntax,
      buffer: JEditBuffer,
      start_line: Int,
      end_line: Int): Iterator[Text.Info[Token]] =
    for {
      line <- Range(start_line min (buffer.getLineCount - 1), end_line max -1, -1).iterator
      tokens <- try_line_tokens(syntax, buffer, line).iterator
      stops =
        tokens.reverseIterator.scanLeft(buffer.getLineEndOffset(line) min buffer.getLength)(
          (i, tok) => i - tok.source.length)
      (i, tok) <- stops zip tokens.reverseIterator
    } yield Text.Info(Text.Range(i - tok.source.length, i), tok)


  /* tokens from offset (inclusive) */

  def token_iterator(syntax: Outer_Syntax, buffer: JEditBuffer, offset: Text.Offset):
      Iterator[Text.Info[Token]] =
    if (JEdit_Lib.buffer_range(buffer).contains(offset))
      line_token_iterator(syntax, buffer, buffer.getLineOfOffset(offset), buffer.getLineCount).
        dropWhile(info => !info.range.contains(offset))
    else Iterator.empty

  def token_reverse_iterator(syntax: Outer_Syntax, buffer: JEditBuffer, offset: Text.Offset):
      Iterator[Text.Info[Token]] =
    if (JEdit_Lib.buffer_range(buffer).contains(offset))
      line_token_reverse_iterator(syntax, buffer, buffer.getLineOfOffset(offset), -1).
        dropWhile(info => !info.range.contains(offset))
    else Iterator.empty


  /* command spans */

  def command_span(syntax: Outer_Syntax, buffer: JEditBuffer, offset: Text.Offset)
    : Option[Text.Info[Command_Span.Span]] =
  {
    val keywords = syntax.keywords

    def maybe_command_start(i: Text.Offset): Option[Text.Info[Token]] =
      token_reverse_iterator(syntax, buffer, i).
        find(info => keywords.is_before_command(info.info) || info.info.is_command)

    def maybe_command_stop(i: Text.Offset): Option[Text.Info[Token]] =
      token_iterator(syntax, buffer, i).
        find(info => keywords.is_before_command(info.info) || info.info.is_command)

    if (JEdit_Lib.buffer_range(buffer).contains(offset)) {
      val start_info =
      {
        val info1 = maybe_command_start(offset)
        info1 match {
          case Some(Text.Info(range1, tok1)) if tok1.is_command =>
            val info2 = maybe_command_start(range1.start - 1)
            info2 match {
              case Some(Text.Info(_, tok2)) if keywords.is_before_command(tok2) => info2
              case _ => info1
            }
          case _ => info1
        }
      }
      val (start_before_command, start, start_next) =
        start_info match {
          case Some(Text.Info(range, tok)) =>
            (keywords.is_before_command(tok), range.start, range.stop)
          case None => (false, 0, 0)
        }

      val stop_info =
      {
        val info1 = maybe_command_stop(start_next)
        info1 match {
          case Some(Text.Info(range1, tok1)) if tok1.is_command && start_before_command =>
            maybe_command_stop(range1.stop)
          case _ => info1
        }
      }
      val stop =
        stop_info match {
          case Some(Text.Info(range, _)) => range.start
          case None => buffer.getLength
        }

      val text = JEdit_Lib.get_text(buffer, Text.Range(start, stop)).getOrElse("")
      val spans = syntax.parse_spans(text)

      (spans.iterator.scanLeft(start)(_ + _.length) zip spans.iterator).
        map({ case (i, span) => Text.Info(Text.Range(i, i + span.length), span) }).
        find(_.range.contains(offset))
    }
    else None
  }

  private def _command_span_iterator(
      syntax: Outer_Syntax,
      buffer: JEditBuffer,
      offset: Text.Offset,
      next_offset: Text.Range => Text.Offset): Iterator[Text.Info[Command_Span.Span]] =
    new Iterator[Text.Info[Command_Span.Span]]
    {
      private var next_span = command_span(syntax, buffer, offset)
      def hasNext: Boolean = next_span.isDefined
      def next(): Text.Info[Command_Span.Span] =
      {
        val span = next_span.getOrElse(Iterator.empty.next())
        next_span = command_span(syntax, buffer, next_offset(span.range))
        span
      }
    }

  def command_span_iterator(syntax: Outer_Syntax, buffer: JEditBuffer, offset: Text.Offset)
      : Iterator[Text.Info[Command_Span.Span]] =
    _command_span_iterator(syntax, buffer, offset max 0, range => range.stop)

  def command_span_reverse_iterator(syntax: Outer_Syntax, buffer: JEditBuffer, offset: Text.Offset)
      : Iterator[Text.Info[Command_Span.Span]] =
    _command_span_iterator(syntax, buffer,
      (offset min buffer.getLength) - 1, range => range.start - 1)


  /* token marker */

  class Marker(
    protected val mode: String,
    protected val opt_buffer: Option[Buffer]) extends TokenMarker
  {
    override def hashCode: Int = (mode, opt_buffer).hashCode
    override def equals(that: Any): Boolean =
      that match {
        case other: Marker => mode == other.mode && opt_buffer == other.opt_buffer
        case _ => false
      }

    override def toString: String =
      opt_buffer match {
        case None => "Marker(" + mode + ")"
        case Some(buffer) => "Marker(" + mode + "," + JEdit_Lib.buffer_name(buffer) + ")"
      }

    override def markTokens(context: TokenMarker.LineContext,
        handler: TokenHandler, raw_line: Segment): TokenMarker.LineContext =
    {
      val line = if (raw_line == null) new Segment else raw_line
      val line_context =
        context match { case c: Line_Context => c case _ => Line_Context.init(mode) }
      val structure = line_context.structure

      val context1 =
      {
        val opt_syntax =
          opt_buffer match {
            case Some(buffer) => Isabelle.buffer_syntax(buffer)
            case None => Isabelle.mode_syntax(mode)
          }
        val (styled_tokens, context1) =
          (line_context.context, opt_syntax) match {
            case (Some(ctxt), _) if mode == "isabelle-ml" || mode == "sml" =>
              val (tokens, ctxt1) = ML_Lex.tokenize_line(mode == "sml", line, ctxt)
              val styled_tokens =
                tokens.map(tok => (JEdit_Rendering.ml_token_markup(tok), tok.source))
              (styled_tokens, new Line_Context(line_context.mode, Some(ctxt1), structure))

            case (Some(ctxt), Some(syntax)) if syntax.has_tokens =>
              val (tokens, ctxt1) = Token.explode_line(syntax.keywords, line, ctxt)
              val structure1 = structure.update(syntax.keywords, tokens)
              val styled_tokens =
                tokens.map(tok => (JEdit_Rendering.token_markup(syntax, tok), tok.source))
              (styled_tokens, new Line_Context(line_context.mode, Some(ctxt1), structure1))

            case _ =>
              val styled_token = (JEditToken.NULL, line.subSequence(0, line.count).toString)
              (List(styled_token), new Line_Context(line_context.mode, None, structure))
          }

        val extended = Syntax_Style.extended(line)
        def special(i: Int): Boolean = extended.isDefinedAt(i) || line.charAt(i) == '\t'

        var offset = 0
        for ((style, token) <- styled_tokens) {
          val length = token.length
          if ((offset until (offset + length)).exists(special)) {
            for ((c, i) <- Codepoint.iterator_offset(token)) {
              val style1 =
                extended.get(offset + i) match {
                  case None => style
                  case Some(ext) => ext(style)
                }
              handler.handleToken(line, style1, offset + i, Character.charCount(c), context1)
            }
          }
          else handler.handleToken(line, style, offset, length, context1)
          offset += length
        }
        handler.handleToken(line, JEditToken.END, line.count, 0, context1)
        context1
      }

      val context2 = context1.intern
      handler.setLineContext(context2)
      context2
    }
  }


  /* mode provider */

  class Mode_Provider(orig_provider: ModeProvider) extends ModeProvider
  {
    for (mode <- orig_provider.getModes) addMode(mode)

    override def loadMode(mode: Mode, xmh: XModeHandler): Unit =
    {
      super.loadMode(mode, xmh)
      Isabelle.mode_token_marker(mode.getName).foreach(mode.setTokenMarker _)
      Isabelle.indent_rule(mode.getName).foreach(indent_rule =>
        Untyped.set[java.util.List[IndentRule]](
          mode, "indentRules", java.util.List.of(indent_rule)))
    }
  }
}
