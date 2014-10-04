/*  Title:      Tools/jEdit/src/bibtex_token_markup.scala
    Author:     Makarius

Bibtex token markup.
*/

package isabelle.jedit


import isabelle._

import org.gjt.sp.jedit.syntax.{Token => JEditToken, TokenMarker, TokenHandler, ParserRuleSet}

import javax.swing.text.Segment


object Bibtex_Token_Markup
{
  /* token style */

  private def token_style(item_kind: String, token: Bibtex.Token): Byte =
    token.kind match {
      case Bibtex.Token.Kind.COMMAND => JEditToken.KEYWORD2
      case Bibtex.Token.Kind.ENTRY => JEditToken.KEYWORD1
      case Bibtex.Token.Kind.KEYWORD => JEditToken.OPERATOR
      case Bibtex.Token.Kind.NAT => JEditToken.LITERAL2
      case Bibtex.Token.Kind.STRING => JEditToken.LITERAL1
      case Bibtex.Token.Kind.IDENT =>
        if (Bibtex.is_month(token.source)) JEditToken.LITERAL3
        else
          Bibtex.get_entry(item_kind) match {
            case Some(entry) if entry.is_required(token.source) => JEditToken.KEYWORD3
            case Some(entry) if entry.is_optional(token.source) => JEditToken.KEYWORD4
            case _ => JEditToken.DIGIT
          }
      case Bibtex.Token.Kind.IGNORED => JEditToken.NULL
      case Bibtex.Token.Kind.ERROR => JEditToken.INVALID
    }


  /* line context */

  private val context_rules = new ParserRuleSet("bibtex", "MAIN")

  private class Line_Context(context: Option[Bibtex.Line_Context])
    extends Token_Markup.Generic_Line_Context[Bibtex.Line_Context](context_rules, context)


  /* token marker */

  class Marker extends TokenMarker
  {
    override def markTokens(context: TokenMarker.LineContext,
        handler: TokenHandler, raw_line: Segment): TokenMarker.LineContext =
    {
      val line_ctxt =
        context match {
          case c: Line_Context => c.context
          case _ => Some(Bibtex.Ignored_Context)
        }
      val line = if (raw_line == null) new Segment else raw_line

      val context1 =
      {
        val (styled_tokens, context1) =
          line_ctxt match {
            case Some(ctxt) =>
              val (chunks, ctxt1) = Bibtex.parse_line(line, ctxt)
              val styled_tokens =
                for { chunk <- chunks; tok <- chunk.tokens }
                yield (token_style(chunk.kind, tok), tok.source)
              (styled_tokens, new Line_Context(Some(ctxt1)))
            case None =>
              val styled_token = (JEditToken.NULL, line.subSequence(0, line.count).toString)
              (List(styled_token), new Line_Context(None))
          }

        var offset = 0
        for ((style, token) <- styled_tokens) {
          val length = token.length
          val end_offset = offset + length
          handler.handleToken(line, style, offset, length, context1)
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
}

