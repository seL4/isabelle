/*  Title:      Tools/jEdit/src/jedit/isabelle_token_marker.scala
    Author:     Fabian Immler, TU Munich

Include isabelle's command- and keyword-declarations live in jEdits
syntax-highlighting.
*/

package isabelle.jedit


import isabelle._

import org.gjt.sp.jedit.buffer.JEditBuffer
import org.gjt.sp.jedit.syntax.{Token, TokenMarker, TokenHandler, ParserRuleSet, SyntaxStyle}
import org.gjt.sp.jedit.textarea.TextArea

import java.awt.Font
import java.awt.font.TextAttribute
import javax.swing.text.Segment;


object Isabelle_Token_Marker
{
  /* extended token styles */

  private val plain_range: Int = Token.ID_COUNT
  private val full_range: Int = 3 * plain_range
  private def check_range(i: Int) { require(0 <= i && i < plain_range) }

  def subscript(i: Byte): Byte = { check_range(i); (i + plain_range).toByte }
  def superscript(i: Byte): Byte = { check_range(i); (i + 2 * plain_range).toByte }

  private def script_style(style: SyntaxStyle, i: Int): SyntaxStyle =
  {
    import scala.collection.JavaConversions._
    val script_font =
      style.getFont.deriveFont(Map(TextAttribute.SUPERSCRIPT -> new java.lang.Integer(i)))
    new SyntaxStyle(style.getForegroundColor, style.getBackgroundColor, script_font)
  }

  def extend_styles(styles: Array[SyntaxStyle]): Array[SyntaxStyle] =
  {
    val new_styles = new Array[SyntaxStyle](full_range)
    for (i <- 0 until plain_range) {
      val style = styles(i)
      new_styles(i) = style
      new_styles(subscript(i.toByte)) = script_style(style, -1)
      new_styles(superscript(i.toByte)) = script_style(style, 1)
    }
    new_styles
  }


  /* line context */

  private val rule_set = new ParserRuleSet("isabelle", "MAIN")
  private class LineContext(val line: Int, prev: LineContext)
    extends TokenMarker.LineContext(rule_set, prev)


  /* mapping to jEdit token types */
  // TODO: as properties or CSS style sheet

  private val command_style: Map[String, Byte] =
  {
    import Token._
    Map[String, Byte](
      Keyword.THY_END -> KEYWORD2,
      Keyword.THY_SCRIPT -> LABEL,
      Keyword.PRF_SCRIPT -> LABEL,
      Keyword.PRF_ASM -> KEYWORD3,
      Keyword.PRF_ASM_GOAL -> KEYWORD3
    ).withDefaultValue(KEYWORD1)
  }

  private val token_style: Map[String, Byte] =
  {
    import Token._
    Map[String, Byte](
      // logical entities
      Markup.TCLASS -> NULL,
      Markup.TYCON -> NULL,
      Markup.FIXED_DECL -> FUNCTION,
      Markup.FIXED -> NULL,
      Markup.CONST_DECL -> FUNCTION,
      Markup.CONST -> NULL,
      Markup.FACT_DECL -> FUNCTION,
      Markup.FACT -> NULL,
      Markup.DYNAMIC_FACT -> LABEL,
      Markup.LOCAL_FACT_DECL -> FUNCTION,
      Markup.LOCAL_FACT -> NULL,
      // inner syntax
      Markup.TFREE -> NULL,
      Markup.FREE -> NULL,
      Markup.TVAR -> NULL,
      Markup.SKOLEM -> NULL,
      Markup.BOUND -> NULL,
      Markup.VAR -> NULL,
      Markup.NUM -> DIGIT,
      Markup.FLOAT -> DIGIT,
      Markup.XNUM -> DIGIT,
      Markup.XSTR -> LITERAL4,
      Markup.LITERAL -> OPERATOR,
      Markup.INNER_COMMENT -> COMMENT1,
      Markup.SORT -> NULL,
      Markup.TYP -> NULL,
      Markup.TERM -> NULL,
      Markup.PROP -> NULL,
      Markup.ATTRIBUTE -> NULL,
      Markup.METHOD -> NULL,
      // ML syntax
      Markup.ML_KEYWORD -> KEYWORD1,
      Markup.ML_DELIMITER -> OPERATOR,
      Markup.ML_IDENT -> NULL,
      Markup.ML_TVAR -> NULL,
      Markup.ML_NUMERAL -> DIGIT,
      Markup.ML_CHAR -> LITERAL1,
      Markup.ML_STRING -> LITERAL1,
      Markup.ML_COMMENT -> COMMENT1,
      Markup.ML_MALFORMED -> INVALID,
      // embedded source text
      Markup.ML_SOURCE -> COMMENT3,
      Markup.DOC_SOURCE -> COMMENT3,
      Markup.ANTIQ -> COMMENT4,
      Markup.ML_ANTIQ -> COMMENT4,
      Markup.DOC_ANTIQ -> COMMENT4,
      // outer syntax
      Markup.KEYWORD -> KEYWORD2,
      Markup.OPERATOR -> OPERATOR,
      Markup.COMMAND -> KEYWORD1,
      Markup.IDENT -> NULL,
      Markup.VERBATIM -> COMMENT3,
      Markup.COMMENT -> COMMENT1,
      Markup.CONTROL -> COMMENT3,
      Markup.MALFORMED -> INVALID,
      Markup.STRING -> LITERAL3,
      Markup.ALTSTRING -> LITERAL1
    ).withDefaultValue(NULL)
  }
}


class Isabelle_Token_Marker(model: Document_Model) extends TokenMarker
{
  override def markTokens(prev: TokenMarker.LineContext,
      handler: TokenHandler, line_segment: Segment): TokenMarker.LineContext =
  {
    val previous = prev.asInstanceOf[Isabelle_Token_Marker.LineContext]
    val line = if (prev == null) 0 else previous.line + 1
    val context = new Isabelle_Token_Marker.LineContext(line, previous)
    val start = model.buffer.getLineStartOffset(line)
    val stop = start + line_segment.count

    val document = model.recent_document()
    def to: Int => Int = model.to_current(document, _)
    def from: Int => Int = model.from_current(document, _)

    /* FIXME
    for (text_area <- Isabelle.jedit_text_areas(model.buffer)
          if Document_View(text_area).isDefined)
      Document_View(text_area).get.set_styles()
    */

    def handle_token(style: Byte, offset: Int, length: Int) =
      handler.handleToken(line_segment, style, offset, length, context)

    var next_x = start
    for {
      (command, command_start) <- document.command_range(from(start), from(stop))
      markup <- document.current_state(command).highlight.flatten
      val abs_start = to(command_start + markup.start)
      val abs_stop = to(command_start + markup.stop)
      if (abs_stop > start)
      if (abs_start < stop)
      val token_start = (abs_start - start) max 0
      val token_length =
        (abs_stop - abs_start) -
        ((start - abs_start) max 0) -
        ((abs_stop - stop) max 0)
    }
    {
      val token_type =
        markup.info match {
          case Command.HighlightInfo(Markup.COMMAND, Some(kind)) =>
            Isabelle_Token_Marker.command_style(kind)
          case Command.HighlightInfo(kind, _) =>
            Isabelle_Token_Marker.token_style(kind)
          case _ => Token.NULL
        }
      if (start + token_start > next_x)
        handle_token(Token.COMMENT1, next_x - start, start + token_start - next_x)
      handle_token(token_type, token_start, token_length)
      next_x = start + token_start + token_length
    }
    if (next_x < stop)
      handle_token(Token.COMMENT1, next_x - start, stop - next_x)

    handle_token(Token.END, line_segment.count, 0)
    handler.setLineContext(context)
    context
  }
}
