/*  Title:      Tools/jEdit/src/text_area_painter.scala
    Author:     Makarius

Painter setup for main jEdit text area, depending on common snapshot.
*/

package isabelle.jedit


import isabelle._

import java.awt.{Graphics2D, Shape, Window, Color}
import java.awt.event.{MouseMotionAdapter, MouseAdapter, MouseEvent,
  FocusAdapter, FocusEvent, WindowEvent, WindowAdapter}
import java.awt.font.TextAttribute
import java.text.AttributedString
import java.util.ArrayList

import org.gjt.sp.util.Log
import org.gjt.sp.jedit.{OperatingSystem, Debug, View}
import org.gjt.sp.jedit.syntax.{DisplayTokenHandler, Chunk}
import org.gjt.sp.jedit.textarea.{TextAreaExtension, TextAreaPainter, TextArea}


class Text_Area_Painter(view: View, text_area: TextArea, get_rendering: () => Isabelle_Rendering)
{
  private val buffer = text_area.getBuffer


  /* robust extension body */

  def robust_body[A](default: A)(body: => A): A =
  {
    try {
      Swing_Thread.require()
      if (buffer == text_area.getBuffer) body
      else {
        Log.log(Log.ERROR, this, ERROR("Implicit change of text area buffer"))
        default
      }
    }
    catch { case t: Throwable => Log.log(Log.ERROR, this, t); default }
  }


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


  /* common painter state */

  @volatile private var painter_rendering: Isabelle_Rendering = null
  @volatile private var painter_clip: Shape = null

  private val set_state = new TextAreaExtension
  {
    override def paintScreenLineRange(gfx: Graphics2D,
      first_line: Int, last_line: Int, physical_lines: Array[Int],
      start: Array[Int], end: Array[Int], y: Int, line_height: Int)
    {
      painter_rendering = get_rendering()
      painter_clip = gfx.getClip
    }
  }

  private val reset_state = new TextAreaExtension
  {
    override def paintScreenLineRange(gfx: Graphics2D,
      first_line: Int, last_line: Int, physical_lines: Array[Int],
      start: Array[Int], end: Array[Int], y: Int, line_height: Int)
    {
      painter_rendering = null
      painter_clip = null
    }
  }

  private def robust_rendering(body: Isabelle_Rendering => Unit)
  {
    robust_body(()) { body(painter_rendering) }
  }


  /* active areas within the text */

  private class Active_Area[A](
    rendering: Isabelle_Rendering => Text.Range => Option[Text.Info[A]])
  {
    private var the_info: Option[Text.Info[A]] = None

    def info: Option[Text.Info[A]] = the_info

    def update(new_info: Option[Text.Info[A]])
    {
      val old_info = the_info
      if (new_info != old_info) {
        for { opt <- List(old_info, new_info); Text.Info(range, _) <- opt }
          JEdit_Lib.invalidate_range(text_area, range)
        the_info = new_info
      }
    }

    def update_rendering(r: Isabelle_Rendering, range: Text.Range)
    { update(rendering(r)(range)) }

    def reset { update(None) }
  }

  // owned by Swing thread

  private var control: Boolean = false

  private val highlight_area = new Active_Area[Color]((r: Isabelle_Rendering) => r.highlight _)
  private val hyperlink_area = new Active_Area[Hyperlink]((r: Isabelle_Rendering) => r.hyperlink _)
  private val active_areas = List(highlight_area, hyperlink_area)
  private def active_reset(): Unit = active_areas.foreach(_.reset)

  private val focus_listener = new FocusAdapter {
    override def focusLost(e: FocusEvent) { active_reset() }
  }

  private val window_listener = new WindowAdapter {
    override def windowIconified(e: WindowEvent) { active_reset() }
    override def windowDeactivated(e: WindowEvent) { active_reset() }
  }

  private val mouse_listener = new MouseAdapter {
    override def mouseClicked(e: MouseEvent) {
      hyperlink_area.info match {
        case Some(Text.Info(range, link)) => link.follow(view)
        case None =>
      }
    }
  }

  private val mouse_motion_listener = new MouseMotionAdapter {
    override def mouseMoved(e: MouseEvent) {
      control = if (OperatingSystem.isMacOS()) e.isMetaDown else e.isControlDown
      if (control && !buffer.isLoading) {
        JEdit_Lib.buffer_lock(buffer) {
          val rendering = get_rendering()
          val mouse_offset = text_area.xyToOffset(e.getX(), e.getY())
          val mouse_range = JEdit_Lib.point_range(buffer, mouse_offset)
          active_areas.foreach(_.update_rendering(rendering, mouse_range))
        }
      }
      else active_reset()
    }
  }


  /* tooltips */

  private val tooltip_painter = new TextAreaExtension
  {
    override def getToolTipText(x: Int, y: Int): String =
    {
      robust_body(null: String) {
        val rendering = get_rendering()
        val offset = text_area.xyToOffset(x, y)
        val range = Text.Range(offset, offset + 1)
        val tip =
          if (control) rendering.tooltip(range)
          else rendering.tooltip_message(range)
        tip.map(Isabelle.tooltip(_)) getOrElse null
      }
    }
  }


  /* text background */

  private val background_painter = new TextAreaExtension
  {
    override def paintScreenLineRange(gfx: Graphics2D,
      first_line: Int, last_line: Int, physical_lines: Array[Int],
      start: Array[Int], end: Array[Int], y: Int, line_height: Int)
    {
      robust_rendering { rendering =>
        val ascent = text_area.getPainter.getFontMetrics.getAscent

        for (i <- 0 until physical_lines.length) {
          if (physical_lines(i) != -1) {
            val line_range = JEdit_Lib.proper_line_range(buffer, start(i), end(i))

            // background color (1)
            for {
              Text.Info(range, color) <- rendering.background1(line_range)
              r <- JEdit_Lib.gfx_range(text_area, range)
            } {
              gfx.setColor(color)
              gfx.fillRect(r.x, y + i * line_height, r.length, line_height)
            }

            // background color (2)
            for {
              Text.Info(range, color) <- rendering.background2(line_range)
              r <- JEdit_Lib.gfx_range(text_area, range)
            } {
              gfx.setColor(color)
              gfx.fillRect(r.x + 2, y + i * line_height + 2, r.length - 4, line_height - 4)
            }

            // squiggly underline
            for {
              Text.Info(range, color) <- rendering.squiggly_underline(line_range)
              r <- JEdit_Lib.gfx_range(text_area, range)
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

  private def paint_chunk_list(rendering: Isabelle_Rendering,
    gfx: Graphics2D, line_start: Text.Offset, head: Chunk, x: Float, y: Float): Float =
  {
    val clip_rect = gfx.getClipBounds
    val painter = text_area.getPainter
    val font_context = painter.getFontRenderContext

    var w = 0.0f
    var chunk = head
    while (chunk != null) {
      val chunk_offset = line_start + chunk.offset
      if (x + w + chunk.width > clip_rect.x &&
          x + w < clip_rect.x + clip_rect.width && chunk.accessable)
      {
        val chunk_range = Text.Range(chunk_offset, chunk_offset + chunk.length)
        val chunk_str = if (chunk.str == null) " " * chunk.length else chunk.str
        val chunk_font = chunk.style.getFont
        val chunk_color = chunk.style.getForegroundColor

        def string_width(s: String): Float =
          if (s.isEmpty) 0.0f
          else chunk_font.getStringBounds(s, font_context).getWidth.toFloat

        val caret_range =
          if (text_area.isCaretVisible)
            JEdit_Lib.point_range(buffer, text_area.getCaretPosition)
          else Text.Range(-1)

        val markup =
          for {
            r1 <- rendering.text_color(chunk_range, chunk_color)
            r2 <- r1.try_restrict(chunk_range)
          } yield r2

        val padded_markup =
          if (markup.isEmpty)
            Iterator(Text.Info(chunk_range, chunk_color))
          else
            Iterator(
              Text.Info(Text.Range(chunk_range.start, markup.head.range.start), chunk_color)) ++
            markup.iterator ++
            Iterator(Text.Info(Text.Range(markup.last.range.stop, chunk_range.stop), chunk_color))

        var x1 = x + w
        gfx.setFont(chunk_font)
        for (Text.Info(range, color) <- padded_markup if !range.is_singularity) {
          val str = chunk_str.substring(range.start - chunk_offset, range.stop - chunk_offset)
          gfx.setColor(color)

          range.try_restrict(caret_range) match {
            case Some(r) if !r.is_singularity =>
              val i = r.start - range.start
              val j = r.stop - range.start
              val s1 = str.substring(0, i)
              val s2 = str.substring(i, j)
              val s3 = str.substring(j)

              if (!s1.isEmpty) gfx.drawString(s1, x1, y)

              val astr = new AttributedString(s2)
              astr.addAttribute(TextAttribute.FONT, chunk_font)
              astr.addAttribute(TextAttribute.FOREGROUND, painter.getCaretColor)
              astr.addAttribute(TextAttribute.SWAP_COLORS, TextAttribute.SWAP_COLORS_ON)
              gfx.drawString(astr.getIterator, x1 + string_width(s1), y)

              if (!s3.isEmpty)
                gfx.drawString(s3, x1 + string_width(str.substring(0, j)), y)

            case _ =>
              gfx.drawString(str, x1, y)
          }
          x1 += string_width(str)
        }
      }
      w += chunk.width
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
      robust_rendering { rendering =>
        val clip = gfx.getClip
        val x0 = text_area.getHorizontalOffset
        val fm = text_area.getPainter.getFontMetrics
        var y0 = y + fm.getHeight - (fm.getLeading + 1) - fm.getDescent

        for (i <- 0 until physical_lines.length) {
          val line = physical_lines(i)
          if (line != -1) {
            val screen_line = first_line + i
            val chunks = text_area.getChunksOfScreenLine(screen_line)
            if (chunks != null) {
              val line_start = buffer.getLineStartOffset(line)
              gfx.clipRect(x0, y + line_height * i, Integer.MAX_VALUE, line_height)
              val w = paint_chunk_list(rendering, gfx, line_start, chunks, x0, y0).toInt
              gfx.clipRect(x0 + w.toInt, 0, Integer.MAX_VALUE, Integer.MAX_VALUE)
              orig_text_painter.paintValidLine(gfx,
                screen_line, line, start(i), end(i), y + line_height * i)
              gfx.setClip(clip)
            }
          }
          y0 += line_height
        }
      }
    }
  }


  /* foreground */

  private val foreground_painter = new TextAreaExtension
  {
    override def paintScreenLineRange(gfx: Graphics2D,
      first_line: Int, last_line: Int, physical_lines: Array[Int],
      start: Array[Int], end: Array[Int], y: Int, line_height: Int)
    {
      robust_rendering { rendering =>
        for (i <- 0 until physical_lines.length) {
          if (physical_lines(i) != -1) {
            val line_range = JEdit_Lib.proper_line_range(buffer, start(i), end(i))

            // foreground color
            for {
              Text.Info(range, color) <- rendering.foreground(line_range)
              r <- JEdit_Lib.gfx_range(text_area, range)
            } {
              gfx.setColor(color)
              gfx.fillRect(r.x, y + i * line_height, r.length, line_height)
            }

            // highlight range -- potentially from other snapshot
            for {
              info <- highlight_area.info
              Text.Info(range, color) <- info.try_restrict(line_range)
              r <- JEdit_Lib.gfx_range(text_area, range)
            } {
              gfx.setColor(color)
              gfx.fillRect(r.x, y + i * line_height, r.length, line_height)
            }

            // hyperlink range -- potentially from other snapshot
            for {
              info <- hyperlink_area.info
              Text.Info(range, _) <- info.try_restrict(line_range)
              r <- JEdit_Lib.gfx_range(text_area, range)
            } {
              gfx.setColor(rendering.hyperlink_color)
              gfx.drawRect(r.x, y + i * line_height, r.length - 1, line_height - 1)
            }
          }
        }
      }
    }
  }


  /* caret -- outside of text range */

  private class Caret_Painter(before: Boolean) extends TextAreaExtension
  {
    override def paintValidLine(gfx: Graphics2D,
      screen_line: Int, physical_line: Int, start: Int, end: Int, y: Int)
    {
      robust_rendering { _ =>
        if (before) gfx.clipRect(0, 0, 0, 0)
        else gfx.setClip(painter_clip)
      }
    }
  }

  private val before_caret_painter1 = new Caret_Painter(true)
  private val after_caret_painter1 = new Caret_Painter(false)
  private val before_caret_painter2 = new Caret_Painter(true)
  private val after_caret_painter2 = new Caret_Painter(false)

  private val caret_painter = new TextAreaExtension
  {
    override def paintValidLine(gfx: Graphics2D,
      screen_line: Int, physical_line: Int, start: Int, end: Int, y: Int)
    {
      robust_rendering { _ =>
        if (text_area.isCaretVisible) {
          val caret = text_area.getCaretPosition
          if (start <= caret && caret == end - 1) {
            val painter = text_area.getPainter
            val fm = painter.getFontMetrics

            val offset = caret - text_area.getLineStartOffset(physical_line)
            val x = text_area.offsetToXY(physical_line, offset).x
            gfx.setColor(painter.getCaretColor)
            gfx.drawRect(x, y, JEdit_Lib.char_width(text_area) - 1, fm.getHeight - 1)
          }
        }
      }
    }
  }


  /* activation */

  def activate()
  {
    val painter = text_area.getPainter
    painter.addExtension(TextAreaPainter.LOWEST_LAYER, set_state)
    painter.addExtension(TextAreaPainter.LINE_BACKGROUND_LAYER + 1, tooltip_painter)
    painter.addExtension(TextAreaPainter.LINE_BACKGROUND_LAYER + 1, background_painter)
    painter.addExtension(TextAreaPainter.TEXT_LAYER, text_painter)
    painter.addExtension(TextAreaPainter.CARET_LAYER - 1, before_caret_painter1)
    painter.addExtension(TextAreaPainter.CARET_LAYER + 1, after_caret_painter1)
    painter.addExtension(TextAreaPainter.BLOCK_CARET_LAYER - 1, before_caret_painter2)
    painter.addExtension(TextAreaPainter.BLOCK_CARET_LAYER + 1, after_caret_painter2)
    painter.addExtension(TextAreaPainter.BLOCK_CARET_LAYER + 2, caret_painter)
    painter.addExtension(500, foreground_painter)
    painter.addExtension(TextAreaPainter.HIGHEST_LAYER, reset_state)
    painter.removeExtension(orig_text_painter)
    painter.addMouseListener(mouse_listener)
    painter.addMouseMotionListener(mouse_motion_listener)
    text_area.addFocusListener(focus_listener)
    view.addWindowListener(window_listener)
  }

  def deactivate()
  {
    val painter = text_area.getPainter
    view.removeWindowListener(window_listener)
    text_area.removeFocusListener(focus_listener)
    painter.removeMouseMotionListener(mouse_motion_listener)
    painter.removeMouseListener(mouse_listener)
    painter.addExtension(TextAreaPainter.TEXT_LAYER, orig_text_painter)
    painter.removeExtension(reset_state)
    painter.removeExtension(foreground_painter)
    painter.removeExtension(caret_painter)
    painter.removeExtension(after_caret_painter2)
    painter.removeExtension(before_caret_painter2)
    painter.removeExtension(after_caret_painter1)
    painter.removeExtension(before_caret_painter1)
    painter.removeExtension(text_painter)
    painter.removeExtension(background_painter)
    painter.removeExtension(tooltip_painter)
    painter.removeExtension(set_state)
  }
}

