/*
 * include isabelle's command- and keyword-declarations
 * live in jEdits syntax-highlighting
 *
 * @author Fabian Immler, TU Munich
 */

package isabelle.jedit


import isabelle.prover.Prover
import isabelle.Markup

import org.gjt.sp.jedit.buffer.JEditBuffer
import org.gjt.sp.jedit.syntax.{Token => JToken,
  TokenMarker, TokenHandler, SyntaxStyle, ParserRuleSet}

import java.awt.Color
import java.awt.Font
import javax.swing.text.Segment;


object DynamicTokenMarker
{
  // Mapping to jEdit token types
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

  private val outer: Set[String] =
    Set(Markup.IDENT, Markup.COMMAND, Markup.KEYWORD, Markup.VERBATIM, Markup.COMMENT,
      Markup.CONTROL, Markup.MALFORMED, Markup.STRING, Markup.ALTSTRING)
  def is_outer(kind: String) = outer.contains(kind)
}


class DynamicTokenMarker(buffer: JEditBuffer, prover: Prover)
  extends TokenMarker
{
  override def markTokens(prev: TokenMarker.LineContext,
      handler: TokenHandler, line_segment: Segment): TokenMarker.LineContext =
  {
    val previous = prev.asInstanceOf[IndexLineContext]
    val line = if (prev == null) 0 else previous.line + 1
    val context = new IndexLineContext(line, previous)
    val start = buffer.getLineStartOffset(line)
    val stop = start + line_segment.count

    val theory_view = Isabelle.prover_setup(buffer).get.theory_view
    val document = theory_view.current_document()
    def to: Int => Int = theory_view.to_current(document, _)
    def from: Int => Int = theory_view.from_current(document, _)

    var command = document.find_command_at(from(start))
    var next_x = start
    while (command != null && command.start(document) < from(stop)) {
      for {
        markup <- command.highlight_node(document).flatten
        abs_stop = to(markup.abs_stop(document))
        abs_start = to(markup.abs_start(document))
        if (abs_stop > start)
        if (abs_start < stop)
        byte = DynamicTokenMarker.choose_byte(markup.info.toString)
        token_start = abs_start - start max 0
        token_length = (abs_stop - abs_start) -
            (start - abs_start max 0) -
            (abs_stop - stop max 0)
      } {
        if (start + token_start > next_x)
          handler.handleToken(line_segment, 1,
            next_x - start, start + token_start - next_x, context)
        handler.handleToken(line_segment, byte,
          token_start, token_length, context)
        next_x = start + token_start + token_length
      }
      command = document.commands.next(command).getOrElse(null)
    }
    if (next_x < stop)
      handler.handleToken(line_segment, 1, next_x - start, stop - next_x, context)

    handler.handleToken(line_segment, JToken.END, line_segment.count, 0, context)
    handler.setLineContext(context)
    return context
  }
}


class IndexLineContext(val line: Int, prev: IndexLineContext)
  extends TokenMarker.LineContext(new ParserRuleSet("isabelle", "MAIN"), prev)
