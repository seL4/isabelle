/*  Title:      Tools/jEdit/src/text_overview.scala
    Author:     Makarius

Swing component for text status overview.
*/

package isabelle.jedit


import isabelle._

import scala.annotation.tailrec

import java.awt.{Graphics, Graphics2D, BorderLayout, Dimension, Color}
import java.awt.event.{MouseAdapter, MouseEvent}
import javax.swing.{JPanel, ToolTipManager}


class Text_Overview(doc_view: Document_View) extends JPanel(new BorderLayout)
{
  private val text_area = doc_view.text_area
  private val buffer = doc_view.model.buffer

  private val WIDTH = 10
  private val HEIGHT = 2

  private def lines(): Int = buffer.getLineCount max text_area.getVisibleLines

  setPreferredSize(new Dimension(WIDTH, 0))

  setRequestFocusEnabled(false)

  addMouseListener(new MouseAdapter {
    override def mousePressed(event: MouseEvent) {
      val line = (event.getY * lines()) / getHeight
      if (line >= 0 && line < text_area.getLineCount)
        text_area.setCaretPosition(text_area.getLineStartOffset(line))
    }
  })

  override def addNotify() {
    super.addNotify()
    ToolTipManager.sharedInstance.registerComponent(this)
  }

  override def removeNotify() {
    ToolTipManager.sharedInstance.unregisterComponent(this)
    super.removeNotify
  }


  /* painting based on cached result */

  private var cached_colors: List[(Color, Int, Int)] = Nil

  private var last_snapshot = Document.State.init.snapshot()
  private var last_options = Isabelle.options.value
  private var last_line_count = 0
  private var last_char_count = 0
  private var last_L = 0
  private var last_H = 0

  override def paintComponent(gfx: Graphics)
  {
    super.paintComponent(gfx)
    Swing_Thread.assert()

    doc_view.rich_text_area.robust_body(()) {
      JEdit_Lib.buffer_lock(buffer) {
        val snapshot = doc_view.model.snapshot()

        if (snapshot.is_outdated) {
          gfx.setColor(Isabelle.options.color_value("outdated_color"))
          gfx.asInstanceOf[Graphics2D].fill(gfx.getClipBounds)
        }
        else {
          gfx.setColor(getBackground)
          gfx.asInstanceOf[Graphics2D].fill(gfx.getClipBounds)

          val line_count = buffer.getLineCount
          val char_count = buffer.getLength

          val L = lines()
          val H = getHeight()

          val options = Isabelle.options.value

          if (!(line_count == last_line_count && char_count == last_char_count &&
                L == last_L && H == last_H && (snapshot eq_markup last_snapshot) &&
                (options eq last_options)))
          {
            val rendering = Isabelle_Rendering(snapshot, options)

            @tailrec def loop(l: Int, h: Int, p: Int, q: Int, colors: List[(Color, Int, Int)])
              : List[(Color, Int, Int)] =
            {
              if (l < line_count && h < H) {
                val p1 = p + H
                val q1 = q + HEIGHT * L
                val (l1, h1) =
                  if (p1 >= q1) (l + 1, h + (p1 - q) / L)
                  else (l + (q1 - p) / H, h + HEIGHT)

                val start = buffer.getLineStartOffset(l)
                val end =
                  if (l1 < line_count) buffer.getLineStartOffset(l1)
                  else char_count
                val range = Text.Range(start, end)

                val colors1 =
                  (rendering.overview_color(range), colors) match {
                    case (Some(color), (old_color, old_h, old_h1) :: rest)
                    if color == old_color && old_h1 == h => (color, old_h, h1) :: rest
                    case (Some(color), _) => (color, h, h1) :: colors
                    case (None, _) => colors
                  }
                loop(l1, h1, p + (l1 - l) * H, q + (h1 - h) * L, colors1)
              }
              else colors.reverse
            }
            cached_colors = loop(0, 0, 0, 0, Nil)

            last_snapshot = snapshot
            last_options = options
            last_line_count = line_count
            last_char_count = char_count
            last_L = L
            last_H = H
          }

          for ((color, h, h1) <- cached_colors) {
            gfx.setColor(color)
            gfx.fillRect(0, h, getWidth, h1 - h)
          }
        }
      }
    }
  }
}

