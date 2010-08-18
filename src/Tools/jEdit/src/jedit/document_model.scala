/*  Title:      Tools/jEdit/src/jedit/document_model.scala
    Author:     Fabian Immler, TU Munich
    Author:     Makarius

Document model connected to jEdit buffer -- single node in theory graph.
*/

package isabelle.jedit


import isabelle._

import scala.actors.Actor, Actor._
import scala.collection.mutable

import org.gjt.sp.jedit.Buffer
import org.gjt.sp.jedit.buffer.{BufferAdapter, BufferListener, JEditBuffer}
import org.gjt.sp.jedit.syntax.{SyntaxStyle, Token, TokenMarker, TokenHandler, ParserRuleSet}
import org.gjt.sp.jedit.textarea.TextArea

import java.awt.font.TextAttribute
import javax.swing.text.Segment;


object Document_Model
{
  object Token_Markup
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
    class LineContext(val line: Int, prev: LineContext)
      extends TokenMarker.LineContext(rule_set, prev)


    /* mapping to jEdit token types */
    // TODO: as properties or CSS style sheet

    val command_style: Map[String, Byte] =
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

    val token_style: Map[String, Byte] =
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


  /* document model of buffer */

  private val key = "isabelle.document_model"

  def init(session: Session, buffer: Buffer, thy_name: String): Document_Model =
  {
    Swing_Thread.require()
    val model = new Document_Model(session, buffer, thy_name)
    buffer.setProperty(key, model)
    model.activate()
    model
  }

  def apply(buffer: Buffer): Option[Document_Model] =
  {
    Swing_Thread.require()
    buffer.getProperty(key) match {
      case model: Document_Model => Some(model)
      case _ => None
    }
  }

  def exit(buffer: Buffer)
  {
    Swing_Thread.require()
    apply(buffer) match {
      case None => error("No document model for buffer: " + buffer)
      case Some(model) =>
        model.deactivate()
        buffer.unsetProperty(key)
    }
  }
}


class Document_Model(val session: Session, val buffer: Buffer, val thy_name: String)
{
  /* visible line end */

  // simplify slightly odd result of TextArea.getLineEndOffset
  // NB: jEdit already normalizes \r\n and \r to \n
  def visible_line_end(start: Text.Offset, end: Text.Offset): Text.Offset =
  {
    val end1 = end - 1
    if (start <= end1 && end1 < buffer.getLength &&
        buffer.getSegment(end1, 1).charAt(0) == '\n') end1
    else end
  }


  /* pending text edits */

  object pending_edits  // owned by Swing thread
  {
    private val pending = new mutable.ListBuffer[Text.Edit]
    def snapshot(): List[Text.Edit] = pending.toList

    private val delay_flush = Swing_Thread.delay_last(session.input_delay) {
      if (!pending.isEmpty) session.edit_version(List((thy_name, flush())))
    }

    def flush(): List[Text.Edit] =
    {
      Swing_Thread.require()
      val edits = snapshot()
      pending.clear
      edits
    }

    def +=(edit: Text.Edit)
    {
      Swing_Thread.require()
      pending += edit
      delay_flush()
    }
  }


  /* snapshot */

  def snapshot(): Document.Snapshot =
  {
    Swing_Thread.require()
    session.snapshot(thy_name, pending_edits.snapshot())
  }


  /* buffer listener */

  private val buffer_listener: BufferListener = new BufferAdapter
  {
    override def contentInserted(buffer: JEditBuffer,
      start_line: Int, offset: Int, num_lines: Int, length: Int)
    {
      pending_edits += Text.Edit.insert(offset, buffer.getText(offset, length))
    }

    override def preContentRemoved(buffer: JEditBuffer,
      start_line: Int, offset: Int, num_lines: Int, removed_length: Int)
    {
      pending_edits += Text.Edit.remove(offset, buffer.getText(offset, removed_length))
    }
  }


  /* semantic token marker */

  private val token_marker = new TokenMarker
  {
    override def markTokens(prev: TokenMarker.LineContext,
        handler: TokenHandler, line_segment: Segment): TokenMarker.LineContext =
    {
      val previous = prev.asInstanceOf[Document_Model.Token_Markup.LineContext]
      val line = if (prev == null) 0 else previous.line + 1
      val context = new Document_Model.Token_Markup.LineContext(line, previous)
      val start = buffer.getLineStartOffset(line)
      val stop = start + line_segment.count

      // FIXME proper synchronization / thread context (!??)
      val snapshot = Swing_Thread.now { Document_Model.this.snapshot() }

      /* FIXME
      for (text_area <- Isabelle.jedit_text_areas(buffer)
            if Document_View(text_area).isDefined)
        Document_View(text_area).get.set_styles()
      */

      def handle_token(style: Byte, offset: Text.Offset, length: Int) =
        handler.handleToken(line_segment, style, offset, length, context)

      var next_x = start
      for {
        (command, command_start) <-
          snapshot.node.command_range(snapshot.revert(start), snapshot.revert(stop))
        markup <- snapshot.state(command).highlight
        val Text.Range(abs_start, abs_stop) = snapshot.convert(markup.range + command_start)
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
              Document_Model.Token_Markup.command_style(kind)
            case Command.HighlightInfo(kind, _) =>
              Document_Model.Token_Markup.token_style(kind)
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


  /* activation */

  def activate()
  {
    buffer.setTokenMarker(token_marker)
    buffer.addBufferListener(buffer_listener)
    buffer.propertiesChanged()
    pending_edits += Text.Edit.insert(0, buffer.getText(0, buffer.getLength))
  }

  def refresh()
  {
    buffer.setTokenMarker(token_marker)
  }

  def deactivate()
  {
    buffer.setTokenMarker(buffer.getMode.getTokenMarker)
    buffer.removeBufferListener(buffer_listener)
  }
}
