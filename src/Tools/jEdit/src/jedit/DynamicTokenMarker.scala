/*
 * include isabelle's command- and keyword-declarations
 * live in jEdits syntax-highlighting
 *
 * @author Fabian Immler, TU Munich
 */

package isabelle.jedit

import isabelle.proofdocument.ProofDocument
import isabelle.prover.{Command, MarkupNode}
import isabelle.Markup

import org.gjt.sp.jedit.buffer.JEditBuffer
import org.gjt.sp.jedit.syntax._

import java.awt.Color
import java.awt.Font
import javax.swing.text.Segment;

object DynamicTokenMarker {

  def styles: Array[SyntaxStyle] = {
    val array = new Array[SyntaxStyle](256)
    // array(0) won't be used: reserved for global default-font
    array(1) = new SyntaxStyle(Color.black, Color.white, Isabelle.plugin.font)
    array(2) = new SyntaxStyle(new Color(255, 0, 255), Color.white, Isabelle.plugin.font)
    array(3) = new SyntaxStyle(Color.blue, Color.white, Isabelle.plugin.font)
    array(4) = new SyntaxStyle(Color.green, Color.white, Isabelle.plugin.font)
    array(5) = new SyntaxStyle(new Color(255, 128, 128), Color.white,Isabelle.plugin.font)
    array(6) = new SyntaxStyle(Color.yellow, Color.white, Isabelle.plugin.font)
    array(7) = new SyntaxStyle( new Color(0, 192, 0), Color.white, Isabelle.plugin.font)
    array(8) = new SyntaxStyle(Color.blue, Color.white, Isabelle.plugin.font)
    array(9) = new SyntaxStyle(Color.green, Color.white, Isabelle.plugin.font)
    array(10) = new SyntaxStyle(Color.gray, Color.white, Isabelle.plugin.font)
    array(11) = new SyntaxStyle(Color.white, Color.white, Isabelle.plugin.font)
    array(12) = new SyntaxStyle(Color.red, Color.white, Isabelle.plugin.font)
    array(13) = new SyntaxStyle(Color.orange, Color.white, Isabelle.plugin.font)
    return array
  }

  def choose_byte(kind: String): Byte = {
    // TODO: as properties
    kind match {
      // logical entities
      case Markup.TCLASS | Markup.TYCON | Markup.FIXED_DECL | Markup.FIXED | Markup.CONST_DECL
        | Markup.CONST | Markup.FACT_DECL | Markup.FACT | Markup.DYNAMIC_FACT
        | Markup.LOCAL_FACT_DECL | Markup.LOCAL_FACT => 2
      // inner syntax
      case Markup.TFREE | Markup.FREE => 3
      case Markup.TVAR | Markup.SKOLEM | Markup.BOUND | Markup.VAR => 4
      case Markup.NUM | Markup.FLOAT | Markup.XNUM | Markup.XSTR | Markup.LITERAL
        | Markup.INNER_COMMENT => 5
      case Markup.SORT | Markup.TYP | Markup.TERM | Markup.PROP
        | Markup.ATTRIBUTE | Markup.METHOD => 6
      // ML syntax
      case Markup.ML_KEYWORD | Markup.ML_IDENT => 8
      case Markup.ML_TVAR => 4
      case Markup.ML_NUMERAL => 5
      case Markup.ML_CHAR | Markup.ML_STRING => 13
      case Markup.ML_COMMENT => 10
      case Markup.ML_MALFORMED => 12
      // embedded source text
      case Markup.ML_SOURCE | Markup.DOC_SOURCE | Markup.ANTIQ | Markup.ML_ANTIQ
        | Markup.DOC_ANTIQ => 7
      // outer syntax
      case Markup.IDENT | Markup.COMMAND | Markup.KEYWORD => 8
      case Markup.VERBATIM => 9
      case Markup.COMMENT => 10
      case Markup.CONTROL => 11
      case Markup.MALFORMED => 12
      case Markup.STRING | Markup.ALTSTRING => 13
      // other
      case _ => 1
    }
  }

  def choose_color(kind : String) : Color = styles((choose_byte(kind).asInstanceOf[Byte])).getForegroundColor

}

class DynamicTokenMarker(buffer: JEditBuffer, document: ProofDocument) extends TokenMarker {

  override def markTokens(prev: TokenMarker.LineContext,
    handler: TokenHandler, line_segment: Segment): TokenMarker.LineContext = {
    val previous = prev.asInstanceOf[IndexLineContext]
    val line = if(prev == null) 0 else previous.line + 1
    val context = new IndexLineContext(line, previous)
    val start = buffer.getLineStartOffset(line)
    val stop = start + line_segment.count
    
    def to = Isabelle.prover_setup(buffer).get.theory_view.to_current(_)
    def from = Isabelle.prover_setup(buffer).get.theory_view.from_current(_)

    val commands = document.commands.dropWhile(_.stop <= from(start))
    if(commands.hasNext) {
      var next_x = start
      for {
        command <- commands.takeWhile(_.start < from(stop))
        markup <- command.root_node.flatten
        if(to(markup.abs_stop) > start)
        if(to(markup.abs_start) < stop)
        byte = DynamicTokenMarker.choose_byte(markup.kind)
        token_start = to(markup.abs_start) - start max 0
        token_length = to(markup.abs_stop) - to(markup.abs_start) -
                       (start - to(markup.abs_start) max 0) -
                       (to(markup.abs_stop) - stop max 0)
      } {
        if (start + token_start > next_x) 
          handler.handleToken(line_segment, 1, next_x - start, start + token_start - next_x, context)
        handler.handleToken(line_segment, byte, token_start, token_length, context)
        next_x = start + token_start + token_length
      }
      if (next_x < stop)
        handler.handleToken(line_segment, 1, next_x - start, stop - next_x, context)
    } else {
      handler.handleToken(line_segment, 1, 0, line_segment.count, context)
    }

    handler.handleToken(line_segment,Token.END, line_segment.count, 0, context)
    handler.setLineContext(context)
    return context
  }

}

class IndexLineContext(val line: Int, prev: IndexLineContext)
  extends TokenMarker.LineContext(new ParserRuleSet("isabelle", "MAIN"), prev)
