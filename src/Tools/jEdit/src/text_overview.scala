/*  Title:      Tools/jEdit/src/text_overview.scala
    Author:     Makarius

Swing component for text status overview.
*/

package isabelle.jedit


import isabelle._

import scala.annotation.tailrec

import java.awt.{Graphics, Graphics2D, BorderLayout, Dimension}
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

  override def paintComponent(gfx: Graphics)
  {
    super.paintComponent(gfx)
    Swing_Thread.assert()

    doc_view.robust_body(()) {
      Isabelle.buffer_lock(buffer) {
        val snapshot = doc_view.model.snapshot()

        gfx.setColor(getBackground)
        gfx.asInstanceOf[Graphics2D].fill(gfx.getClipBounds)

        val line_count = buffer.getLineCount
        val char_count = buffer.getLength

        val L = lines()
        val H = getHeight()

        @tailrec def paint_loop(l: Int, h: Int, p: Int, q: Int): Unit =
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

            Isabelle_Rendering.overview_color(snapshot, Text.Range(start, end)) match {
              case None =>
              case Some(color) =>
                gfx.setColor(color)
                gfx.fillRect(0, h, getWidth, h1 - h)
            }
            paint_loop(l1, h1, p + (l1 - l) * H, q + (h1 - h) * L)
          }
        }
        paint_loop(0, 0, 0, 0)
      }
    }
  }
}

