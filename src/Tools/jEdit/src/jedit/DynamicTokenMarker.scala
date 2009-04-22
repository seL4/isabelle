/*
 * include isabelle's command- and keyword-declarations
 * live in jEdits syntax-highlighting
 *
 * @author Fabian Immler, TU Munich
 */

package isabelle.jedit

import isabelle.prover.{Command, MarkupNode, Prover}
import isabelle.Markup

import org.gjt.sp.jedit.buffer.JEditBuffer
import org.gjt.sp.jedit.syntax._

import java.awt.Color
import java.awt.Font
import javax.swing.text.Segment;

object DynamicTokenMarker {

  // Mapping to jEdits token types
  def choose_byte(kind: String): Byte = {
    // TODO: as properties
    kind match {
      // logical entities
      case Markup.TCLASS | Markup.TYCON | Markup.FIXED_DECL | Markup.FIXED | Markup.CONST_DECL
        | Markup.CONST | Markup.FACT_DECL | Markup.FACT | Markup.DYNAMIC_FACT
        | Markup.LOCAL_FACT_DECL | Markup.LOCAL_FACT => Token.DIGIT
      // inner syntax
      case Markup.TFREE | Markup.FREE => Token.LITERAL2
      case Markup.TVAR | Markup.SKOLEM | Markup.BOUND | Markup.VAR => Token.LITERAL3
      case Markup.NUM | Markup.FLOAT | Markup.XNUM | Markup.XSTR | Markup.LITERAL
        | Markup.INNER_COMMENT => Token.LITERAL4
      case Markup.SORT | Markup.TYP | Markup.TERM | Markup.PROP
        | Markup.ATTRIBUTE | Markup.METHOD => Token.FUNCTION
      // ML syntax
      case Markup.ML_KEYWORD => Token.KEYWORD2
      case Markup.ML_IDENT => Token.KEYWORD3
      case Markup.ML_TVAR => Token.LITERAL3
      case Markup.ML_NUMERAL => Token.LITERAL4
      case Markup.ML_CHAR | Markup.ML_STRING => Token.LITERAL1
      case Markup.ML_COMMENT => Token.COMMENT1
      case Markup.ML_MALFORMED => Token.INVALID
      // embedded source text
      case Markup.ML_SOURCE | Markup.DOC_SOURCE | Markup.ANTIQ | Markup.ML_ANTIQ
        | Markup.DOC_ANTIQ => Token.COMMENT4
      // outer syntax
      case Markup.IDENT => Token.KEYWORD3
      case Markup.COMMAND => Token.KEYWORD1
      case Markup.KEYWORD => Token.KEYWORD2
      case Markup.VERBATIM => Token.COMMENT1
      case Markup.COMMENT => Token.COMMENT2
      case Markup.CONTROL => Token.COMMENT3
      case Markup.MALFORMED => Token.INVALID
      case Markup.STRING | Markup.ALTSTRING => Token.LITERAL1
      // other
      case _ => 0
    }
  }

  def choose_color(kind : String, styles: Array[SyntaxStyle]) : Color =
    styles((choose_byte(kind).asInstanceOf[Byte])).getForegroundColor

}

class DynamicTokenMarker(buffer: JEditBuffer, prover: Prover) extends TokenMarker {

  override def markTokens(prev: TokenMarker.LineContext,
    handler: TokenHandler, line_segment: Segment): TokenMarker.LineContext = {
    val previous = prev.asInstanceOf[IndexLineContext]
    val line = if(prev == null) 0 else previous.line + 1
    val context = new IndexLineContext(line, previous)
    val start = buffer.getLineStartOffset(line)
    val stop = start + line_segment.count

    val document = prover.document

    def to: Int => Int = Isabelle.prover_setup(buffer).get.theory_view.to_current(document.id, _)
    def from: Int => Int = Isabelle.prover_setup(buffer).get.theory_view.from_current(document.id, _)

    var next_x = start
    for {
      command <- document.commands.dropWhile(_.stop(document) <= from(start)).takeWhile(_.start(document) < from(stop))
      markup <- command.root_node.flatten
      if(to(markup.abs_stop(document)) > start)
      if(to(markup.abs_start(document)) < stop)
      byte = DynamicTokenMarker.choose_byte(markup.kind)
      token_start = to(markup.abs_start(document)) - start max 0
      token_length = to(markup.abs_stop(document)) - to(markup.abs_start(document)) -
                     (start - to(markup.abs_start(document)) max 0) -
                     (to(markup.abs_stop(document)) - stop max 0)
    } {
      if (start + token_start > next_x)
        handler.handleToken(line_segment, 1, next_x - start, start + token_start - next_x, context)
      handler.handleToken(line_segment, byte, token_start, token_length, context)
      next_x = start + token_start + token_length
    }
    if (next_x < stop)
      handler.handleToken(line_segment, 1, next_x - start, stop - next_x, context)

    handler.handleToken(line_segment,Token.END, line_segment.count, 0, context)
    handler.setLineContext(context)
    return context
  }

}

class IndexLineContext(val line: Int, prev: IndexLineContext)
  extends TokenMarker.LineContext(new ParserRuleSet("isabelle", "MAIN"), prev)
