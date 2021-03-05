/*  Title:      Tools/jEdit/src/text_overview.scala
    Author:     Makarius

GUI component for text status overview.
*/

package isabelle.jedit


import isabelle._

import scala.annotation.tailrec

import java.awt.{Graphics, Graphics2D, BorderLayout, Dimension, Color}
import java.awt.event.{MouseAdapter, MouseEvent}
import javax.swing.{JPanel, ToolTipManager}


class Text_Overview(doc_view: Document_View) extends JPanel(new BorderLayout)
{
  /* GUI components */

  private val text_area = doc_view.text_area
  private val buffer = doc_view.model.buffer

  private def lines(): Int = buffer.getLineCount max text_area.getVisibleLines

  private val WIDTH = text_area.getPainter.getFontMetrics.stringWidth("A") max 10
  private val HEIGHT = 4

  setPreferredSize(new Dimension(WIDTH, 0))

  setRequestFocusEnabled(false)

  addMouseListener(new MouseAdapter {
    override def mousePressed(event: MouseEvent): Unit =
    {
      val line = (event.getY * lines()) / getHeight
      if (line >= 0 && line < text_area.getLineCount)
        text_area.setCaretPosition(text_area.getLineStartOffset(line))
    }
  })

  override def addNotify(): Unit =
  {
    super.addNotify()
    ToolTipManager.sharedInstance.registerComponent(this)
  }

  override def removeNotify(): Unit =
  {
    ToolTipManager.sharedInstance.unregisterComponent(this)
    super.removeNotify
  }


  /* overview */

  private case class Overview(
    line_count: Int = 0,
    char_count: Int = 0,
    L: Int = 0,
    H: Int = 0)

  private def get_overview(): Overview =
    Overview(
      line_count = buffer.getLineCount,
      char_count = buffer.getLength,
      L = lines(),
      H = getHeight())


  /* synchronous painting */

  type Color_Info = (Rendering.Color.Value, Int, Int)

  private var current_colors: List[Color_Info] = Nil
  private var current_overview = Overview()

  private val delay_repaint =
    Delay.first(PIDE.options.seconds("editor_update_delay"), gui = true) { repaint() }

  override def paintComponent(gfx: Graphics): Unit =
  {
    super.paintComponent(gfx)
    GUI_Thread.assert {}

    doc_view.rich_text_area.robust_body(()) {
      JEdit_Lib.buffer_lock(buffer) {
        val rendering = doc_view.get_rendering()
        val overview = get_overview()

        if (rendering.snapshot.is_outdated || overview != current_overview) {
          invoke()
          delay_repaint.invoke()

          gfx.setColor(rendering.outdated_color)
          gfx.asInstanceOf[Graphics2D].fill(gfx.getClipBounds)
        }
        else {
          gfx.setColor(getBackground)
          gfx.asInstanceOf[Graphics2D].fill(gfx.getClipBounds)
          for ((color, h, h1) <- current_colors) {
            gfx.setColor(rendering.color(color))
            gfx.fillRect(0, h, getWidth, h1 - h)
          }
        }
      }
    }
  }


  /* asynchronous refresh */

  private val future_refresh = Synchronized(Future.value(()))
  private def is_running(): Boolean = !future_refresh.value.is_finished

  def invoke(): Unit = delay_refresh.invoke()
  def revoke(): Unit = { delay_refresh.revoke(); future_refresh.change(x => { x.cancel(); x }) }

  private val delay_refresh =
    Delay.first(PIDE.options.seconds("editor_update_delay"), gui = true) {
      if (!doc_view.rich_text_area.check_robust_body) invoke()
      else {
        JEdit_Lib.buffer_lock(buffer) {
          val rendering = doc_view.get_rendering()
          val overview = get_overview()

          if (rendering.snapshot.is_outdated || is_running()) invoke()
          else {
            val line_offsets =
            {
              val line_manager = JEdit_Lib.buffer_line_manager(buffer)
              val a = new Array[Int](line_manager.getLineCount)
              for (i <- 1 until a.length) a(i) = line_manager.getLineEndOffset(i - 1)
              a
            }

            future_refresh.change(_ =>
              Future.fork {
                val line_count = overview.line_count
                val char_count = overview.char_count
                val L = overview.L
                val H = overview.H

                @tailrec def loop(l: Int, h: Int, p: Int, q: Int, colors: List[Color_Info])
                  : List[Color_Info] =
                {
                  Exn.Interrupt.expose()

                  if (l < line_count && h < H) {
                    val p1 = p + H
                    val q1 = q + HEIGHT * L
                    val (l1, h1) =
                      if (p1 >= q1) (l + 1, h + (p1 - q) / L)
                      else (l + (q1 - p) / H, h + HEIGHT)

                    val start = line_offsets(l)
                    val end =
                      if (l1 < line_count) line_offsets(l1)
                      else char_count

                    val colors1 =
                      (rendering.overview_color(Text.Range(start, end)), colors) match {
                        case (Some(color), (old_color, old_h, old_h1) :: rest)
                        if color == old_color && old_h1 == h => (color, old_h, h1) :: rest
                        case (Some(color), _) => (color, h, h1) :: colors
                        case (None, _) => colors
                      }
                    loop(l1, h1, p + (l1 - l) * H, q + (h1 - h) * L, colors1)
                  }
                  else colors.reverse
                }
                val new_colors = loop(0, 0, 0, 0, Nil)

                GUI_Thread.later {
                  current_overview = overview
                  current_colors = new_colors
                  repaint()
                }
              }
            )
          }
        }
      }
    }
}
