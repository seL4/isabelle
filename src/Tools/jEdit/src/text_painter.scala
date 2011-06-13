/*  Title:      Tools/jEdit/src/text_painter.scala
    Author:     Makarius

Replacement painter for jEdit text area.
*/

package isabelle.jedit


import isabelle._

import java.awt.{Graphics, Graphics2D}
import java.util.ArrayList

import org.gjt.sp.jedit.Debug
import org.gjt.sp.jedit.syntax.{DisplayTokenHandler, Chunk}
import org.gjt.sp.jedit.textarea.{JEditTextArea, TextAreaExtension, TextAreaPainter}


class Text_Painter(doc_view: Document_View) extends TextAreaExtension
{
  private val text_area = doc_view.text_area

  private val orig_text_painter: TextAreaExtension =
  {
    val name = "org.gjt.sp.jedit.textarea.TextAreaPainter$PaintText"
    text_area.getPainter.getExtensions.iterator.filter(x => x.getClass.getName == name).toList
    match {
      case List(x) => x
      case _ => error("Expected exactly one " + name)
    }
  }

  override def paintScreenLineRange(gfx: Graphics2D,
    first_line: Int, last_line: Int, physical_lines: Array[Int],
    start: Array[Int], end: Array[Int], y_start: Int, line_height: Int)
  {
    val buffer = text_area.getBuffer
    Isabelle.swing_buffer_lock(buffer) {
      val painter = text_area.getPainter
      val font = painter.getFont
      val font_context = painter.getFontRenderContext
      val font_metrics = painter.getFontMetrics

      def paint_chunk_list(head_offset: Text.Offset, head: Chunk, x: Float, y: Float): Float =
      {
        val clip_rect = gfx.getClipBounds

        var w = 0.0f
        var offset = head_offset
        var chunk = head
        while (chunk != null) {
          val chunk_length = if (chunk.str == null) 0 else chunk.str.length

          if (x + w + chunk.width > clip_rect.x &&
              x + w < clip_rect.x + clip_rect.width &&
              chunk.accessable && chunk.visible)
          {
            val chunk_range = Text.Range(offset, offset + chunk_length)
            val chunk_font = chunk.style.getFont
            val chunk_color = chunk.style.getForegroundColor

            val markup =
              doc_view.text_area_snapshot.select_markup(chunk_range)(Isabelle_Markup.foreground)

            gfx.setFont(chunk_font)
            if (!Debug.DISABLE_GLYPH_VECTOR && chunk.gv != null &&
                markup.forall(info => info.info.isEmpty)) {
              gfx.setColor(chunk_color)
              gfx.drawGlyphVector(chunk.gv, x + w, y)
            }
            else {
              var xpos = x + w
              for (Text.Info(range, info) <- markup) {
                val str = chunk.str.substring(range.start - offset, range.stop - offset)
                gfx.setColor(info.getOrElse(chunk_color))
                gfx.drawString(str, xpos.toInt, y.toInt)
                xpos += chunk_font.getStringBounds(str, font_context).getWidth.toFloat
              }
            }
          }
          w += chunk.width
          offset += chunk_length
          chunk = chunk.next.asInstanceOf[Chunk]
        }
        w
      }

      // see org.gjt.sp.jedit.textarea.TextArea.propertiesChanged
      // see org.gjt.sp.jedit.textarea.TextArea.setMaxLineLength
      val char_width = font.getStringBounds(" ", font_context).getWidth.round.toInt
      val soft_wrap = buffer.getStringProperty("wrap") == "soft"
      val wrap_margin =
      {
        val max = buffer.getIntegerProperty("maxLineLen", 0)
        if (max > 0) font.getStringBounds(" " * max, font_context).getWidth.toInt
        else if (soft_wrap) painter.getWidth - char_width * 3
        else 0
      }.toFloat

      val line_infos: Map[Text.Offset, Chunk] =
      {
        val out = new ArrayList[Chunk]
        val handler = new DisplayTokenHandler
        val margin = if (soft_wrap) wrap_margin else 0.0f

        var result = Map[Text.Offset, Chunk]()
        for (line <- physical_lines.iterator.filter(i => i != -1)) {
          out.clear
          handler.init(painter.getStyles, font_context, painter, out, margin)
          buffer.markTokens(line, handler)

          val line_start = buffer.getLineStartOffset(line)
          for (i <- 0 until out.size) {
            val chunk = out.get(i)
            result += (line_start + chunk.offset -> chunk)
          }
        }
        result
      }

      val clip = gfx.getClip
      val x0 = text_area.getHorizontalOffset
      var y0 =
        y_start + font_metrics.getHeight - (font_metrics.getLeading + 1) - font_metrics.getDescent

      for (i <- 0 until physical_lines.length) {
        if (physical_lines(i) != -1) {
          line_infos.get(start(i)) match {
            case Some(chunk) =>
              val w = paint_chunk_list(start(i), chunk, x0, y0).toInt
              gfx.clipRect(x0 + w, 0, Integer.MAX_VALUE, Integer.MAX_VALUE)
              orig_text_painter.paintValidLine(gfx,
                first_line + i, physical_lines(i), start(i), end(i), y_start + line_height * i)
              gfx.setClip(clip)

            case None =>
          }
        }
        y0 += line_height
      }
    }
  }


  /* activation */

  def activate()
  {
    val painter = text_area.getPainter
    painter.removeExtension(orig_text_painter)
    painter.addExtension(TextAreaPainter.TEXT_LAYER, this)
  }

  def deactivate()
  {
    val painter = text_area.getPainter
    painter.removeExtension(this)
    painter.addExtension(TextAreaPainter.TEXT_LAYER, orig_text_painter)
  }
}

