/*  Title:      Tools/jEdit/src/jedit/document_model.scala
    Author:     Fabian Immler, TU Munich
    Author:     Makarius

Document model connected to jEdit buffer -- single node in theory graph.
*/

package isabelle.jedit


import isabelle._

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

    private val dummy_rules = new ParserRuleSet("isabelle", "MAIN")

    class Line_Context(val line: Int, prev: Line_Context)
      extends TokenMarker.LineContext(dummy_rules, prev)
    {
      override def hashCode: Int = line
      override def equals(that: Any) =
        that match {
          case other: Line_Context => line == other.line
          case _ => false
        }
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
      Isabelle.swing_buffer_lock(buffer) {
        val snapshot = Document_Model.this.snapshot()

        val previous = prev.asInstanceOf[Document_Model.Token_Markup.Line_Context]
        val line = if (prev == null) 0 else previous.line + 1
        val context = new Document_Model.Token_Markup.Line_Context(line, previous)

        val start = buffer.getLineStartOffset(line)
        val stop = start + line_segment.count

        /* FIXME
        for (text_area <- Isabelle.jedit_text_areas(buffer)
              if Document_View(text_area).isDefined)
          Document_View(text_area).get.set_styles()
        */

        def handle_token(style: Byte, offset: Text.Offset, length: Int) =
          handler.handleToken(line_segment, style, offset, length, context)

        val syntax = session.current_syntax()
        val tokens = snapshot.select_markup(Text.Range(start, stop))(Isabelle_Markup.tokens(syntax))

        var last = start
        for (token <- tokens.iterator) {
          val Text.Range(token_start, token_stop) = token.range
          if (last < token_start)
            handle_token(Token.COMMENT1, last - start, token_start - last)
          handle_token(token.info getOrElse Token.NULL,
            token_start - start, token_stop - token_start)
          last = token_stop
        }
        if (last < stop) handle_token(Token.COMMENT1, last - start, stop - last)

        handle_token(Token.END, line_segment.count, 0)
        handler.setLineContext(context)
        context
      }
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
