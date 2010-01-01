/*
 * include isabelle's command- and keyword-declarations
 * live in jEdits syntax-highlighting
 *
 * @author Fabian Immler, TU Munich
 */

package isabelle.jedit


import isabelle.Markup

import org.gjt.sp.jedit.buffer.JEditBuffer
import org.gjt.sp.jedit.syntax.{Token => JToken,
  TokenMarker, TokenHandler, SyntaxStyle, ParserRuleSet}

import java.awt.Color
import java.awt.Font
import javax.swing.text.Segment;


object Isabelle_Token_Marker
{
  /* line context */

  private val rule_set = new ParserRuleSet("isabelle", "MAIN")
  private class LineContext(val line: Int, prev: LineContext)
    extends TokenMarker.LineContext(rule_set, prev)


  /* mapping to jEdit token types */
  // TODO: as properties or CSS style sheet

  private val choose_byte: Map[String, Byte] =
  {
    import JToken._
    Map[String, Byte](
      // logical entities
      Markup.TCLASS -> LABEL,
      Markup.TYCON -> LABEL,
      Markup.FIXED_DECL -> LABEL,
      Markup.FIXED -> LABEL,
      Markup.CONST_DECL -> LABEL,
      Markup.CONST -> LABEL,
      Markup.FACT_DECL -> LABEL,
      Markup.FACT -> LABEL,
      Markup.DYNAMIC_FACT -> LABEL,
      Markup.LOCAL_FACT_DECL -> LABEL,
      Markup.LOCAL_FACT -> LABEL,
      // inner syntax
      Markup.TFREE -> LITERAL2,
      Markup.FREE -> LITERAL2,
      Markup.TVAR -> LITERAL3,
      Markup.SKOLEM -> LITERAL3,
      Markup.BOUND -> LITERAL3,
      Markup.VAR -> LITERAL3,
      Markup.NUM -> DIGIT,
      Markup.FLOAT -> DIGIT,
      Markup.XNUM -> DIGIT,
      Markup.XSTR -> LITERAL4,
      Markup.LITERAL -> LITERAL4,
      Markup.INNER_COMMENT -> COMMENT1,
      Markup.SORT -> FUNCTION,
      Markup.TYP -> FUNCTION,
      Markup.TERM -> FUNCTION,
      Markup.PROP -> FUNCTION,
      Markup.ATTRIBUTE -> FUNCTION,
      Markup.METHOD -> FUNCTION,
      // ML syntax
      Markup.ML_KEYWORD -> KEYWORD2,
      Markup.ML_IDENT -> NULL,
      Markup.ML_TVAR -> LITERAL3,
      Markup.ML_NUMERAL -> DIGIT,
      Markup.ML_CHAR -> LITERAL1,
      Markup.ML_STRING -> LITERAL1,
      Markup.ML_COMMENT -> COMMENT1,
      Markup.ML_MALFORMED -> INVALID,
      // embedded source text
      Markup.ML_SOURCE -> COMMENT4,
      Markup.DOC_SOURCE -> COMMENT4,
      Markup.ANTIQ -> COMMENT4,
      Markup.ML_ANTIQ -> COMMENT4,
      Markup.DOC_ANTIQ -> COMMENT4,
      // outer syntax
      Markup.IDENT -> NULL,
      Markup.COMMAND -> OPERATOR,
      Markup.KEYWORD -> KEYWORD4,
      Markup.VERBATIM -> COMMENT3,
      Markup.COMMENT -> COMMENT1,
      Markup.CONTROL -> COMMENT3,
      Markup.MALFORMED -> INVALID,
      Markup.STRING -> LITERAL3,
      Markup.ALTSTRING -> LITERAL1
    ).withDefaultValue(NULL)
  }

  def choose_color(kind: String, styles: Array[SyntaxStyle]): Color =
    styles(choose_byte(kind)).getForegroundColor
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

    var next_x = start
    var cmd = document.command_at(from(start))
    while (cmd.isDefined && cmd.get.start(document) < from(stop)) {
      val command = cmd.get
      for {
        markup <- command.highlight(document).flatten
        command_start = command.start(document)
        abs_start = to(command_start + markup.start)
        abs_stop = to(command_start + markup.stop)
        if (abs_stop > start)
        if (abs_start < stop)
        byte = Isabelle_Token_Marker.choose_byte(markup.info.toString)
        token_start = (abs_start - start) max 0
        token_length =
          (abs_stop - abs_start) -
          ((start - abs_start) max 0) -
          ((abs_stop - stop) max 0)
      } {
        if (start + token_start > next_x)
          handler.handleToken(line_segment, 1,
            next_x - start, start + token_start - next_x, context)
        handler.handleToken(line_segment, byte,
          token_start, token_length, context)
        next_x = start + token_start + token_length
      }
      cmd = document.commands.next(command)
    }
    if (next_x < stop)
      handler.handleToken(line_segment, 1, next_x - start, stop - next_x, context)

    handler.handleToken(line_segment, JToken.END, line_segment.count, 0, context)
    handler.setLineContext(context)
    return context
  }
}
