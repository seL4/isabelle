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

  var styles : Array[SyntaxStyle] = null
  def reload_styles: Array[SyntaxStyle] = {
    styles = new Array[SyntaxStyle](256)
    //jEdit styles
    for(i <- 0 to Token.ID_COUNT) styles(i) = new SyntaxStyle(Color.black, Color.white, Isabelle.plugin.font)
    //isabelle styles
    def from_property(kind : String, spec : String, default : Color) : Color = 
      try {Color.decode(Isabelle.Property("styles." + kind + "." + spec))} catch {case _ => default}

    for((kind, i) <- kinds) styles(i + FIRST_BYTE) = new SyntaxStyle(
      from_property(kind, "foreground", Color.black),
      from_property(kind, "background", Color.white),
      Isabelle.plugin.font)
    return styles
  }

  private final val FIRST_BYTE : Byte = 30
  val kinds = List(// TODO Markups as Enumeration?
     // default style
    null,
    // logical entities
    Markup.TCLASS, Markup.TYCON, Markup.FIXED_DECL, Markup.FIXED, Markup.CONST_DECL,
    Markup.CONST, Markup.FACT_DECL, Markup.FACT, Markup.DYNAMIC_FACT,
    Markup.LOCAL_FACT_DECL, Markup.LOCAL_FACT,
    // inner syntax
    Markup.TFREE, Markup.FREE,
    Markup.TVAR, Markup.SKOLEM, Markup.BOUND, Markup.VAR,
    Markup.NUM, Markup.FLOAT, Markup.XNUM, Markup.XSTR, Markup.LITERAL,
    Markup.INNER_COMMENT,
    Markup.SORT, Markup.TYP, Markup.TERM, Markup.PROP,
    Markup.ATTRIBUTE, Markup.METHOD,
    // embedded source text
    Markup.ML_SOURCE, Markup.DOC_SOURCE, Markup.ANTIQ, Markup.ML_ANTIQ,
    Markup.DOC_ANTIQ,
    // outer syntax
    Markup.IDENT, Markup.COMMAND, Markup.KEYWORD, Markup.VERBATIM, Markup.COMMENT,
    Markup.CONTROL, Markup.MALFORMED, Markup.STRING, Markup.ALTSTRING
  ).zipWithIndex

  def choose_byte(kind : String) : Byte = (kinds.find (k => kind == k._1)) match {
    case Some((kind, index)) => (index + FIRST_BYTE).asInstanceOf[Byte]
    case _ => FIRST_BYTE
  }

  def choose_color(kind : String) : Color = styles((choose_byte(kind).asInstanceOf[Byte])).getForegroundColor

}

class DynamicTokenMarker(buffer: JEditBuffer, prover: Prover) extends TokenMarker {

  override def markTokens(prev: TokenMarker.LineContext,
    handler: TokenHandler, line_segment: Segment): TokenMarker.LineContext = {
    val previous = prev.asInstanceOf[IndexLineContext]
    val line = if(prev == null) 0 else previous.line + 1
    val context = new IndexLineContext(line, previous)
    val start = buffer.getLineStartOffset(line)
    val stop = start + line_segment.count

    val (current_document, current_version) = synchronized (prover.document, prover.document_id)
   
    def to = Isabelle.prover_setup(buffer).get.theory_view.to_current(_)
    def from = Isabelle.prover_setup(buffer).get.theory_view.from_current(_)

    var next_x = start
    for {
      command <- prover.document.commands.dropWhile(_.stop <= from(start)).takeWhile(_.start < from(stop))
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

    handler.handleToken(line_segment,Token.END, line_segment.count, 0, context)
    handler.setLineContext(context)
    return context
  }

}

class IndexLineContext(val line: Int, prev: IndexLineContext)
  extends TokenMarker.LineContext(new ParserRuleSet("isabelle", "MAIN"), prev)
