/*  Title:      Tools/jEdit/src/text_area_painter.scala
    Author:     Makarius

Painter setup for main jEdit text area.
*/

package isabelle.jedit


import isabelle._

import java.awt.Graphics2D
import java.awt.font.TextAttribute
import java.text.AttributedString
import java.util.ArrayList

import org.gjt.sp.jedit.Debug
import org.gjt.sp.jedit.syntax.{DisplayTokenHandler, Chunk}
import org.gjt.sp.jedit.textarea.{TextAreaExtension, TextAreaPainter, JEditTextArea}


class Text_Area_Painter(doc_view: Document_View)
{
  private val model = doc_view.model
  private val buffer = model.buffer
  private val text_area = doc_view.text_area


  /* original painters */

  private def pick_extension(name: String): TextAreaExtension =
  {
    text_area.getPainter.getExtensions.iterator.filter(x => x.getClass.getName == name).toList
    match {
      case List(x) => x
      case _ => error("Expected exactly one " + name)
    }
  }

  private val orig_text_painter =
    pick_extension("org.gjt.sp.jedit.textarea.TextAreaPainter$PaintText")

  private val orig_caret_painter =
    pick_extension("org.gjt.sp.jedit.textarea.TextAreaPainter$PaintCaret")


  /* painter snapshot */

  @volatile private var _painter_snapshot: Option[Document.Snapshot] = None

  private def painter_snapshot(): Document.Snapshot =
    _painter_snapshot match {
      case Some(snapshot) => snapshot
      case None => error("Missing document snapshot for text area painter")
    }

  private val set_snapshot = new TextAreaExtension
  {
    override def paintScreenLineRange(gfx: Graphics2D,
      first_line: Int, last_line: Int, physical_lines: Array[Int],
      start: Array[Int], end: Array[Int], y: Int, line_height: Int)
    {
      _painter_snapshot = Some(model.snapshot())
    }
  }

  private val reset_snapshot = new TextAreaExtension
  {
    override def paintScreenLineRange(gfx: Graphics2D,
      first_line: Int, last_line: Int, physical_lines: Array[Int],
      start: Array[Int], end: Array[Int], y: Int, line_height: Int)
    {
      _painter_snapshot = None
    }
  }


  /* text background */

  private val background_painter = new TextAreaExtension
  {
    override def paintScreenLineRange(gfx: Graphics2D,
      first_line: Int, last_line: Int, physical_lines: Array[Int],
      start: Array[Int], end: Array[Int], y: Int, line_height: Int)
    {
      Isabelle.swing_buffer_lock(buffer) {
        val snapshot = painter_snapshot()
        val ascent = text_area.getPainter.getFontMetrics.getAscent

        for (i <- 0 until physical_lines.length) {
          if (physical_lines(i) != -1) {
            val line_range = doc_view.proper_line_range(start(i), end(i))

            // background color: status
            val cmds = snapshot.node.command_range(snapshot.revert(line_range))
            for {
              (command, command_start) <- cmds if !command.is_ignored
              val range = line_range.restrict(snapshot.convert(command.range + command_start))
              r <- Isabelle.gfx_range(text_area, range)
              color <- Isabelle_Markup.status_color(snapshot, command)
            } {
              gfx.setColor(color)
              gfx.fillRect(r.x, y + i * line_height, r.length, line_height)
            }

            // background color (1): markup
            for {
              Text.Info(range, Some(color)) <-
                snapshot.select_markup(line_range)(Isabelle_Markup.background1).iterator
              r <- Isabelle.gfx_range(text_area, range)
            } {
              gfx.setColor(color)
              gfx.fillRect(r.x, y + i * line_height, r.length, line_height)
            }

            // background color (2): markup
            for {
              Text.Info(range, Some(color)) <-
                snapshot.select_markup(line_range)(Isabelle_Markup.background2).iterator
              r <- Isabelle.gfx_range(text_area, range)
            } {
              gfx.setColor(color)
              gfx.fillRect(r.x + 2, y + i * line_height + 2, r.length - 4, line_height - 4)
            }

            // sub-expression highlighting -- potentially from other snapshot
            doc_view.highlight_range match {
              case Some((range, color)) if line_range.overlaps(range) =>
                Isabelle.gfx_range(text_area, line_range.restrict(range)) match {
                  case None =>
                  case Some(r) =>
                    gfx.setColor(color)
                    gfx.drawRect(r.x, y + i * line_height, r.length - 1, line_height - 1)
                }
              case _ =>
            }

            // squiggly underline
            for {
              Text.Info(range, Some(color)) <-
                snapshot.select_markup(line_range)(Isabelle_Markup.message).iterator
              r <- Isabelle.gfx_range(text_area, range)
            } {
              gfx.setColor(color)
              val x0 = (r.x / 2) * 2
              val y0 = r.y + ascent + 1
              for (x1 <- Range(x0, x0 + r.length, 2)) {
                val y1 = if (x1 % 4 < 2) y0 else y0 + 1
                gfx.drawLine(x1, y1, x1 + 1, y1)
              }
            }
          }
        }
      }
    }
  }


  /* text */

  private def line_infos(physical_lines: Iterator[Int]): Map[Text.Offset, Chunk] =
  {
    val painter = text_area.getPainter
    val font = painter.getFont
    val font_context = painter.getFontRenderContext

    // see org.gjt.sp.jedit.textarea.TextArea.propertiesChanged
    // see org.gjt.sp.jedit.textarea.TextArea.setMaxLineLength
    val margin =
      if (buffer.getStringProperty("wrap") != "soft") 0.0f
      else {
        val max = buffer.getIntegerProperty("maxLineLen", 0)
        if (max > 0) font.getStringBounds(" " * max, font_context).getWidth.toInt
        else painter.getWidth - font.getStringBounds(" ", font_context).getWidth.round.toInt * 3
      }.toFloat

    val out = new ArrayList[Chunk]
    val handler = new DisplayTokenHandler

    var result = Map[Text.Offset, Chunk]()
    for (line <- physical_lines) {
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

  private def paint_chunk_list(gfx: Graphics2D,
    offset: Text.Offset, caret_offset: Text.Offset, head: Chunk, x: Float, y: Float): Float =
  {
    val clip_rect = gfx.getClipBounds
    val painter = text_area.getPainter
    val font_context = painter.getFontRenderContext

    var w = 0.0f
    var chunk_offset = offset
    var chunk = head
    while (chunk != null) {
      val chunk_length = if (chunk.str == null) 0 else chunk.str.length

      if (x + w + chunk.width > clip_rect.x &&
          x + w < clip_rect.x + clip_rect.width &&
          chunk.accessable && chunk.visible)
      {
        val chunk_range = Text.Range(chunk_offset, chunk_offset + chunk_length)
        val chunk_font = chunk.style.getFont
        val chunk_color = chunk.style.getForegroundColor

        val markup = painter_snapshot.select_markup(chunk_range)(Isabelle_Markup.foreground)

        gfx.setFont(chunk_font)
        if (!Debug.DISABLE_GLYPH_VECTOR && chunk.gv != null &&
            markup.forall(info => info.info.isEmpty) &&
            !chunk_range.contains(caret_offset)) {
          gfx.setColor(chunk_color)
          gfx.drawGlyphVector(chunk.gv, x + w, y)
        }
        else {
          var x1 = x + w
          for (Text.Info(range, info) <- markup) {
            val str = chunk.str.substring(range.start - chunk_offset, range.stop - chunk_offset)
            gfx.setColor(info.getOrElse(chunk_color))
            if (range.contains(caret_offset)) {
              val astr = new AttributedString(str)
              val i = caret_offset - range.start
              astr.addAttribute(TextAttribute.FONT, chunk_font)
              astr.addAttribute(TextAttribute.FOREGROUND, painter.getCaretColor, i, i + 1)
              astr.addAttribute(TextAttribute.SWAP_COLORS, TextAttribute.SWAP_COLORS_ON, i, i + 1)
              gfx.drawString(astr.getIterator, x1.toInt, y.toInt)
            }
            else {
              gfx.drawString(str, x1.toInt, y.toInt)
            }
            x1 += chunk_font.getStringBounds(str, font_context).getWidth.toFloat
          }
        }
      }
      w += chunk.width
      chunk_offset += chunk_length
      chunk = chunk.next.asInstanceOf[Chunk]
    }
    w
  }

  private val text_painter = new TextAreaExtension
  {
    override def paintScreenLineRange(gfx: Graphics2D,
      first_line: Int, last_line: Int, physical_lines: Array[Int],
      start: Array[Int], end: Array[Int], y: Int, line_height: Int)
    {
      Isabelle.swing_buffer_lock(buffer) {
        val clip = gfx.getClip
        val x0 = text_area.getHorizontalOffset
        val fm = text_area.getPainter.getFontMetrics
        var y0 = y + fm.getHeight - (fm.getLeading + 1) - fm.getDescent

        val caret_offset =
          if (text_area.hasFocus) text_area.getCaretPosition
          else -1

        val infos = line_infos(physical_lines.iterator.filter(i => i != -1))
        for (i <- 0 until physical_lines.length) {
          if (physical_lines(i) != -1) {
            val x1 =
              infos.get(start(i)) match {
                case None => x0
                case Some(chunk) =>
                  gfx.clipRect(x0, y + line_height * i, Integer.MAX_VALUE, line_height)
                  val w = paint_chunk_list(gfx, start(i), caret_offset, chunk, x0, y0).toInt
                  x0 + w.toInt
              }
            gfx.clipRect(x1, 0, Integer.MAX_VALUE, Integer.MAX_VALUE)
            orig_text_painter.paintValidLine(gfx,
              first_line + i, physical_lines(i), start(i), end(i), y + line_height * i)
            orig_caret_painter.paintValidLine(gfx,
              first_line + i, physical_lines(i), start(i), end(i), y + line_height * i)
            gfx.setClip(clip)
          }
          y0 += line_height
        }
      }
    }
  }


  /* activation */

  def activate()
  {
    val painter = text_area.getPainter
    painter.addExtension(TextAreaPainter.LOWEST_LAYER, set_snapshot)
    painter.addExtension(TextAreaPainter.LINE_BACKGROUND_LAYER + 1, background_painter)
    painter.addExtension(TextAreaPainter.TEXT_LAYER, text_painter)
    painter.addExtension(TextAreaPainter.HIGHEST_LAYER, reset_snapshot)
    painter.removeExtension(orig_text_painter)
    painter.removeExtension(orig_caret_painter)
  }

  def deactivate()
  {
    val painter = text_area.getPainter
    val caret_layer =
      if (painter.isBlockCaretEnabled) TextAreaPainter.BLOCK_CARET_LAYER
      else TextAreaPainter.CARET_LAYER
    painter.addExtension(caret_layer, orig_caret_painter)
    painter.addExtension(TextAreaPainter.TEXT_LAYER, orig_text_painter)
    painter.removeExtension(reset_snapshot)
    painter.removeExtension(text_painter)
    painter.removeExtension(background_painter)
    painter.removeExtension(set_snapshot)
  }
}

