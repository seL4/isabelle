/*  Title:      Tools/jEdit/src/rich_text_area.scala
    Author:     Makarius

Enhanced version of jEdit text area, with rich text rendering,
tooltips, hyperlinks etc.
*/

package isabelle.jedit


import isabelle._

import java.awt.{Graphics2D, Shape, Color, Point, Cursor, MouseInfo}
import java.awt.event.{MouseMotionAdapter, MouseAdapter, MouseEvent,
  FocusAdapter, FocusEvent, WindowEvent, WindowAdapter, KeyEvent}
import java.awt.font.TextAttribute
import javax.swing.SwingUtilities
import java.text.AttributedString

import scala.util.matching.Regex

import org.gjt.sp.util.Log
import org.gjt.sp.jedit.View
import org.gjt.sp.jedit.syntax.Chunk
import org.gjt.sp.jedit.textarea.{TextAreaExtension, TextAreaPainter, TextArea}


class Rich_Text_Area(
  view: View,
  text_area: TextArea,
  get_rendering: () => JEdit_Rendering,
  close_action: () => Unit,
  get_search_pattern: () => Option[Regex],
  caret_update: () => Unit,
  caret_visible: Boolean,
  enable_hovering: Boolean)
{
  private val buffer = text_area.getBuffer


  /* robust extension body */

  def check_robust_body: Boolean =
    GUI_Thread.require { buffer == text_area.getBuffer }

  def robust_body[A](default: A)(body: => A): A =
  {
    try {
      if (check_robust_body) body
      else {
        Log.log(Log.ERROR, this, ERROR("Implicit change of text area buffer"))
        default
      }
    }
    catch { case exn: Throwable => Log.log(Log.ERROR, this, exn); default }
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


  /* caret focus modifier */

  @volatile private var caret_focus_modifier = false

  def caret_focus_range: Text.Range =
    if (caret_focus_modifier) Text.Range.full
    else JEdit_Lib.visible_range(text_area) getOrElse Text.Range.offside

  private val key_listener =
    JEdit_Lib.key_listener(
      key_pressed = (evt: KeyEvent) =>
      {
        val mod = PIDE.options.string("jedit_focus_modifier")
        val old = caret_focus_modifier
        caret_focus_modifier = (mod.nonEmpty && mod == JEdit_Lib.modifier_string(evt))
        if (caret_focus_modifier != old) caret_update()
      },
      key_released = _ =>
      {
        if (caret_focus_modifier) {
          caret_focus_modifier = false
          caret_update()
        }
      })


  /* common painter state */

  @volatile private var painter_rendering: JEdit_Rendering = null
  @volatile private var painter_clip: Shape = null
  @volatile private var caret_focus = Rendering.Focus.empty

  private val set_state = new TextAreaExtension
  {
    override def paintScreenLineRange(gfx: Graphics2D,
      first_line: Int, last_line: Int, physical_lines: Array[Int],
      start: Array[Int], end: Array[Int], y: Int, line_height: Int): Unit =
    {
      painter_rendering = get_rendering()
      painter_clip = gfx.getClip
      caret_focus =
        if (caret_enabled && !painter_rendering.snapshot.is_outdated) {
          painter_rendering.caret_focus(JEdit_Lib.caret_range(text_area), caret_focus_range)
        }
        else Rendering.Focus.empty
    }
  }

  private val reset_state = new TextAreaExtension
  {
    override def paintScreenLineRange(gfx: Graphics2D,
      first_line: Int, last_line: Int, physical_lines: Array[Int],
      start: Array[Int], end: Array[Int], y: Int, line_height: Int): Unit =
    {
      painter_rendering = null
      painter_clip = null
      caret_focus = Rendering.Focus.empty
    }
  }

  def robust_rendering(body: JEdit_Rendering => Unit): Unit =
  {
    robust_body(()) { body(painter_rendering) }
  }


  /* active areas within the text */

  private class Active_Area[A](
    rendering: JEdit_Rendering => Text.Range => Option[Text.Info[A]],
    cursor: Option[Int])
  {
    private var the_text_info: Option[(String, Text.Info[A])] = None

    def is_active: Boolean = the_text_info.isDefined
    def text_info: Option[(String, Text.Info[A])] = the_text_info
    def info: Option[Text.Info[A]] = the_text_info.map(_._2)

    def update(new_info: Option[Text.Info[A]]): Unit =
    {
      val old_text_info = the_text_info
      val new_text_info =
        new_info.map(info => (text_area.getText(info.range.start, info.range.length), info))

      if (new_text_info != old_text_info) {
        caret_update()
        if (cursor.isDefined) {
          if (new_text_info.isDefined)
            text_area.getPainter.setCursor(Cursor.getPredefinedCursor(cursor.get))
          else
            text_area.getPainter.resetCursor()
        }
        for {
          r0 <- JEdit_Lib.visible_range(text_area)
          opt <- List(old_text_info, new_text_info)
          (_, Text.Info(r1, _)) <- opt
          r2 <- r1.try_restrict(r0)  // FIXME more precise?!
        } JEdit_Lib.invalidate_range(text_area, r2)
        the_text_info = new_text_info
      }
    }

    def update_rendering(r: JEdit_Rendering, range: Text.Range): Unit =
      update(rendering(r)(range))

    def reset(): Unit = update(None)
  }

  // owned by GUI thread

  private val highlight_area =
    new Active_Area[Color](
      (rendering: JEdit_Rendering) => rendering.highlight, None)

  private val hyperlink_area =
    new Active_Area[PIDE.editor.Hyperlink](
      (rendering: JEdit_Rendering) => rendering.hyperlink, Some(Cursor.HAND_CURSOR))

  private val active_area =
    new Active_Area[XML.Elem](
      (rendering: JEdit_Rendering) => rendering.active, Some(Cursor.DEFAULT_CURSOR))

  private val active_areas =
    List((highlight_area, true), (hyperlink_area, true), (active_area, false))
  def active_reset(): Unit = active_areas.foreach(_._1.reset())

  private def area_active(): Boolean =
    active_areas.exists({ case (area, _) => area.is_active })

  private val focus_listener = new FocusAdapter {
    override def focusLost(e: FocusEvent): Unit = { robust_body(()) { active_reset() } }
  }

  private val window_listener = new WindowAdapter {
    override def windowIconified(e: WindowEvent): Unit = { robust_body(()) { active_reset() } }
    override def windowDeactivated(e: WindowEvent): Unit = { robust_body(()) { active_reset() } }
  }

  private val mouse_listener = new MouseAdapter {
    override def mouseClicked(e: MouseEvent): Unit =
    {
      robust_body(()) {
        hyperlink_area.info match {
          case Some(Text.Info(range, link)) =>
            if (!link.external) {
              try { text_area.moveCaretPosition(range.start) }
              catch {
                case _: ArrayIndexOutOfBoundsException =>
                case _: IllegalArgumentException =>
              }
              text_area.requestFocus()
            }
            link.follow(view)
          case None =>
        }
        active_area.text_info match {
          case Some((text, Text.Info(_, markup))) =>
            Active.action(view, text, markup)
            close_action()
          case None =>
        }
      }
    }
  }

  private def mouse_inside_painter(): Boolean =
    MouseInfo.getPointerInfo match {
      case null => false
      case info =>
        val point = info.getLocation
        val painter = text_area.getPainter
        SwingUtilities.convertPointFromScreen(point, painter)
        painter.contains(point)
    }

  private val mouse_motion_listener = new MouseMotionAdapter {
    override def mouseDragged(evt: MouseEvent): Unit =
    {
      robust_body(()) {
        active_reset()
        Completion_Popup.Text_Area.dismissed(text_area)
        Pretty_Tooltip.dismiss_descendant(text_area.getPainter)
      }
    }

    override def mouseMoved(evt: MouseEvent): Unit =
    {
      robust_body(()) {
        val x = evt.getX
        val y = evt.getY
        val control = JEdit_Lib.command_modifier(evt)

        if ((control || enable_hovering) && !buffer.isLoading) {
          JEdit_Lib.buffer_lock(buffer) {
            JEdit_Lib.pixel_range(text_area, x, y) match {
              case None => active_reset()
              case Some(range) =>
                val rendering = get_rendering()
                for ((area, require_control) <- active_areas)
                {
                  if (control == require_control && !rendering.snapshot.is_outdated)
                    area.update_rendering(rendering, range)
                  else area.reset()
                }
            }
          }
        }
        else active_reset()

        if (evt.getSource == text_area.getPainter) {
          Pretty_Tooltip.invoke(() =>
            robust_body(()) {
              if (mouse_inside_painter()) {
                val rendering = get_rendering()
                val snapshot = rendering.snapshot
                if (!snapshot.is_outdated) {
                  JEdit_Lib.pixel_range(text_area, x, y) match {
                    case None =>
                    case Some(range) =>
                      rendering.tooltip(range, control) match {
                        case None =>
                        case Some(tip) =>
                          val painter = text_area.getPainter
                          val loc = new Point(x, y + painter.getLineHeight / 2)
                          val results = snapshot.command_results(tip.range)
                          Pretty_Tooltip(view, painter, loc, rendering, results, tip)
                      }
                  }
                }
              }
          })
        }
      }
    }
  }


  /* text background */

  private val background_painter = new TextAreaExtension
  {
    override def paintScreenLineRange(gfx: Graphics2D,
      first_line: Int, last_line: Int, physical_lines: Array[Int],
      start: Array[Int], end: Array[Int], y: Int, line_height: Int): Unit =
    {
      robust_rendering { rendering =>
        val fm = text_area.getPainter.getFontMetrics

        for (i <- physical_lines.indices) {
          if (physical_lines(i) != -1) {
            val line_range = Text.Range(start(i), end(i) min buffer.getLength)

            // line background color
            for { (c, separator) <- rendering.line_background(line_range) }
            {
              gfx.setColor(rendering.color(c))
              val sep = if (separator) 2 min (line_height / 2) else 0
              gfx.fillRect(0, y + i * line_height, text_area.getWidth, line_height - sep)
            }

            // background color
            for {
              Text.Info(range, c) <-
                rendering.background(Rendering.background_elements, line_range, caret_focus)
              r <- JEdit_Lib.gfx_range(text_area, range)
            } {
              gfx.setColor(rendering.color(c))
              gfx.fillRect(r.x, y + i * line_height, r.length, line_height)
            }

            // active area -- potentially from other snapshot
            for {
              info <- active_area.info
              Text.Info(range, _) <- info.try_restrict(line_range)
              r <- JEdit_Lib.gfx_range(text_area, range)
            } {
              gfx.setColor(rendering.active_hover_color)
              gfx.fillRect(r.x, y + i * line_height, r.length, line_height)
            }

            // squiggly underline
            for {
              Text.Info(range, c) <- rendering.squiggly_underline(line_range)
              r <- JEdit_Lib.gfx_range(text_area, range)
            } {
              gfx.setColor(rendering.color(c))
              val x0 = (r.x / 2) * 2
              val y0 = r.y + fm.getAscent + 1
              for (x1 <- Range(x0, x0 + r.length, 2)) {
                val y1 = if (x1 % 4 < 2) y0 else y0 + 1
                gfx.drawLine(x1, y1, x1 + 1, y1)
              }
            }

            // spell checker
            for {
              spell_checker <- PIDE.plugin.spell_checker.get
              spell <- rendering.spell_checker(line_range)
              text <- JEdit_Lib.get_text(buffer, spell.range)
              info <- spell_checker.marked_words(spell.range.start, text)
              r <- JEdit_Lib.gfx_range(text_area, info.range)
            } {
              gfx.setColor(rendering.spell_checker_color)
              val y0 = r.y + ((fm.getAscent + 4) min (line_height - 2))
              gfx.drawLine(r.x, y0, r.x + r.length, y0)
            }
          }
        }
      }
    }
  }


  /* text */

  private def caret_enabled: Boolean =
    caret_visible && (!text_area.hasFocus || text_area.isCaretVisible)

  private def caret_color(rendering: JEdit_Rendering, offset: Text.Offset): Color =
  {
    if (text_area.isCaretVisible) text_area.getPainter.getCaretColor
    else {
      val debug_positions =
        (for {
          c <- PIDE.session.debugger.focus().iterator
          pos <- c.debug_position.iterator
        } yield pos).toList
      if (debug_positions.exists(PIDE.editor.is_hyperlink_position(rendering.snapshot, offset, _)))
        rendering.caret_debugger_color
      else rendering.caret_invisible_color
    }
  }

  private def paint_chunk_list(rendering: JEdit_Rendering,
    gfx: Graphics2D, line_start: Text.Offset, head: Chunk, x: Float, y: Float): Float =
  {
    val clip_rect = gfx.getClipBounds

    val caret_range =
      if (caret_enabled) JEdit_Lib.caret_range(text_area)
      else Text.Range.offside

    var w = 0.0f
    var chunk = head
    while (chunk != null) {
      val chunk_offset = line_start + chunk.offset
      if (x + w + chunk.width > clip_rect.x &&
          x + w < clip_rect.x + clip_rect.width && chunk.length > 0)
      {
        val chunk_range = Text.Range(chunk_offset, chunk_offset + chunk.length)
        val chunk_str =
          if (chunk.chars == null) Symbol.spaces(chunk.length)
          else {
            if (chunk.str == null) { chunk.str = new String(chunk.chars) }
            chunk.str
          }
        val chunk_font = chunk.style.getFont
        val chunk_color = chunk.style.getForegroundColor

        val chunk_text = new AttributedString(chunk_str)

        def chunk_attrib(attrib: TextAttribute, value: AnyRef, r: Text.Range): Unit =
          chunk_text.addAttribute(attrib, value, r.start - chunk_offset, r.stop - chunk_offset)

        // font
        chunk_text.addAttribute(TextAttribute.RUN_DIRECTION, TextAttribute.RUN_DIRECTION_LTR)
        chunk_text.addAttribute(TextAttribute.FONT, chunk_font)
        if (chunk.usedFontSubstitution) {
          for {
            (c, i) <- Codepoint.iterator_offset(chunk_str) if !chunk_font.canDisplay(c)
            subst_font = Chunk.getSubstFont(c) if subst_font != null
          } {
            val r = Text.Range(i, i + Character.charCount(c)) + chunk_offset
            val font = Chunk.deriveSubstFont(chunk_font, subst_font)
            chunk_attrib(TextAttribute.FONT, font, r)
          }
        }

        // color
        chunk_text.addAttribute(TextAttribute.FOREGROUND, chunk_color)
        for {
          Text.Info(r1, color) <- rendering.text_color(chunk_range, chunk_color).iterator
          r2 <- r1.try_restrict(chunk_range) if !r2.is_singularity
        } chunk_attrib(TextAttribute.FOREGROUND, color, r2)

        // caret
        for { r <- caret_range.try_restrict(chunk_range) if !r.is_singularity } {
          chunk_attrib(TextAttribute.FOREGROUND, caret_color(rendering, r.start), r)
          chunk_attrib(TextAttribute.SWAP_COLORS, TextAttribute.SWAP_COLORS_ON, r)
        }

        gfx.drawString(chunk_text.getIterator, x + w, y)
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
      start: Array[Int], end: Array[Int], y: Int, line_height: Int): Unit =
    {
      robust_rendering { rendering =>
        val painter = text_area.getPainter
        val fm = painter.getFontMetrics
        val lm = painter.getFont.getLineMetrics(" ", painter.getFontRenderContext)

        val clip = gfx.getClip
        val x0 = text_area.getHorizontalOffset
        var y0 = y + painter.getLineHeight - (fm.getLeading + 1) - fm.getDescent

        val (bullet_x, bullet_y, bullet_w, bullet_h) =
        {
          val w = fm.charWidth(' ')
          val b = (w / 2) max 1
          val c = (lm.getAscent + lm.getStrikethroughOffset).round
          ((w - b + 1) / 2, c - b / 2, w - b, line_height - b)
        }

        for (i <- physical_lines.indices) {
          val line = physical_lines(i)
          if (line != -1) {
            val line_range = Text.Range(start(i), end(i) min buffer.getLength)

            // text chunks
            val screen_line = first_line + i
            val chunks = text_area.getChunksOfScreenLine(screen_line)
            if (chunks != null) {
              try {
                val line_start = buffer.getLineStartOffset(line)
                gfx.clipRect(x0, y + line_height * i, Integer.MAX_VALUE, line_height)
                val w = paint_chunk_list(rendering, gfx, line_start, chunks, x0.toFloat, y0.toFloat)
                gfx.clipRect(x0 + w.toInt, 0, Integer.MAX_VALUE, Integer.MAX_VALUE)
                orig_text_painter.paintValidLine(gfx,
                  screen_line, line, start(i), end(i), y + line_height * i)
              } finally { gfx.setClip(clip) }
            }

            // bullet bar
            for {
              Text.Info(range, color) <- rendering.bullet(line_range)
              r <- JEdit_Lib.gfx_range(text_area, range)
            } {
              gfx.setColor(color)
              gfx.fillRect(r.x + bullet_x, y + i * line_height + bullet_y,
                r.length - bullet_w, line_height - bullet_h)
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
      start: Array[Int], end: Array[Int], y: Int, line_height: Int): Unit =
    {
      robust_rendering { rendering =>
        val search_pattern = get_search_pattern()
        for (i <- physical_lines.indices) {
          if (physical_lines(i) != -1) {
            val line_range = Text.Range(start(i), end(i) min buffer.getLength)

            // foreground color
            for {
              Text.Info(range, c) <- rendering.foreground(line_range)
              r <- JEdit_Lib.gfx_range(text_area, range)
            } {
              gfx.setColor(rendering.color(c))
              gfx.fillRect(r.x, y + i * line_height, r.length, line_height)
            }

            // search pattern
            for {
              regex <- search_pattern
              text <- JEdit_Lib.get_text(buffer, line_range)
              m <- regex.findAllMatchIn(text)
              range = Text.Range(m.start, m.end) + line_range.start
              r <- JEdit_Lib.gfx_range(text_area, range)
            } {
              gfx.setColor(rendering.search_color)
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

            // entity def range
            if (!area_active() && caret_visible) {
              for {
                Text.Info(range, color) <- rendering.entity_ref(line_range, caret_focus)
                r <- JEdit_Lib.gfx_range(text_area, range)
              } {
                gfx.setColor(color)
                gfx.drawRect(r.x, y + i * line_height, r.length - 1, line_height - 1)
              }
            }

            // completion range
            if (!area_active() && caret_visible) {
              for {
                completion <- Completion_Popup.Text_Area(text_area)
                Text.Info(range, color) <- completion.rendering(rendering, line_range)
                r <- JEdit_Lib.gfx_range(text_area, range)
              } {
                gfx.setColor(color)
                gfx.drawRect(r.x, y + i * line_height, r.length - 1, line_height - 1)
              }
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
      screen_line: Int, physical_line: Int, start: Int, end: Int, y: Int): Unit =
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
      screen_line: Int, physical_line: Int, start: Int, end: Int, y: Int): Unit =
    {
      robust_rendering { rendering =>
        if (caret_visible) {
          val caret = text_area.getCaretPosition
          if (caret_enabled && start <= caret && caret == end - 1) {
            val painter = text_area.getPainter
            val fm = painter.getFontMetrics

            val offset = caret - text_area.getLineStartOffset(physical_line)
            val x = text_area.offsetToXY(physical_line, offset).x
            val y1 = y + painter.getLineHeight - (fm.getLeading + 1) - fm.getDescent

            val astr = new AttributedString(" ")
            astr.addAttribute(TextAttribute.FONT, painter.getFont)
            astr.addAttribute(TextAttribute.FOREGROUND, caret_color(rendering, caret))
            astr.addAttribute(TextAttribute.SWAP_COLORS, TextAttribute.SWAP_COLORS_ON)

            val clip = gfx.getClip
            try {
              gfx.clipRect(x, y, Integer.MAX_VALUE, painter.getLineHeight)
              gfx.drawString(astr.getIterator, x, y1)
            }
            finally { gfx.setClip(clip) }
          }
        }
      }
    }
  }


  /* activation */

  def activate(): Unit =
  {
    val painter = text_area.getPainter
    painter.addExtension(TextAreaPainter.LOWEST_LAYER, set_state)
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
    text_area.addKeyListener(key_listener)
    text_area.addFocusListener(focus_listener)
    view.addWindowListener(window_listener)
  }

  def deactivate(): Unit =
  {
    active_reset()
    val painter = text_area.getPainter
    view.removeWindowListener(window_listener)
    text_area.removeFocusListener(focus_listener)
    text_area.removeKeyListener(key_listener)
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
    painter.removeExtension(set_state)
  }
}
