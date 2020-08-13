/*  Title:      Tools/jEdit/src/ml_status.scala
    Author:     Makarius

ML status bar: heap and garbage collection.
*/

package isabelle.jedit


import isabelle._

import java.awt.{Color, Dimension, Graphics, Graphics2D, Insets, RenderingHints}
import java.awt.font.FontRenderContext
import java.awt.event.{MouseAdapter, MouseEvent}
import javax.swing.{JComponent, JLabel}

import org.gjt.sp.jedit.{View, jEdit}
import org.gjt.sp.jedit.gui.statusbar.{StatusWidgetFactory, Widget}


object ML_Status
{
  private val template = "99999/99999MB"

  private class GUI(view: View) extends JComponent
  {
    /* component state -- owned by GUI thread */

    private var status = ML_Statistics.memory_status(Nil)


    /* init */

    setFont(new JLabel().getFont)
    setToolTipText("ML heap memory")

    private val font_render_context = new FontRenderContext(null, true, false)
    private val line_metrics = getFont.getLineMetrics(template, font_render_context)

    {
      val bounds = getFont.getStringBounds(template, font_render_context)
      val dim = new Dimension(bounds.getWidth.toInt, bounds.getHeight.toInt)
      setPreferredSize(dim)
      setMaximumSize(dim)
    }

    setForeground(jEdit.getColorProperty("view.status.foreground"))
    setBackground(jEdit.getColorProperty("view.status.background"))

    def progress_foreground: Color = jEdit.getColorProperty("view.status.memory.foreground")
    def progress_background: Color = jEdit.getColorProperty("view.status.memory.background")


    /* paint */

    private def update(new_status: ML_Statistics.Memory_Status)
    {
      if (status != new_status) {
        status = new_status
        repaint()
      }
    }

    override def paintComponent(gfx: Graphics)
    {
      super.paintComponent(gfx)

      val insets = new Insets(0, 0, 0, 0)

      val width = getWidth - insets.left - insets.right
      val height = getHeight - insets.top - insets.bottom - 1

      val (text, fraction) =
        status.gc_progress match {
          case Some(p) => ("ML cleanup", 1.0 - p)
          case None =>
            ((status.heap_used / 1024 / 1024) + "/" + (status.heap_size / 1024 / 1024) + "MB",
              status.heap_used_fraction)
        }

      val width_fraction = (width * fraction).toInt

      val text_bounds = gfx.getFont.getStringBounds(text, font_render_context)
      val text_x = insets.left + ((width - text_bounds.getWidth).toInt / 2)
      val text_y = (insets.top + line_metrics.getAscent).toInt

      gfx.asInstanceOf[Graphics2D].
        setRenderingHint(
          RenderingHints.KEY_TEXT_ANTIALIASING,
          RenderingHints.VALUE_TEXT_ANTIALIAS_ON)

      gfx.setColor(progress_background)
      gfx.fillRect(insets.left, insets.top, width_fraction, height)

      gfx.setColor(progress_foreground)
      gfx.setClip(insets.left, insets.top, width_fraction, height)
      gfx.drawString(text, text_x, text_y)

      gfx.setColor(getForeground)
      gfx.setClip(insets.left + width_fraction, insets.top,
        getWidth - insets.left - width_fraction, height)
      gfx.drawString(text, text_x, text_y)
    }


    /* main */

    private val main =
      Session.Consumer[Session.Runtime_Statistics](getClass.getName) {
        case stats =>
          val status = ML_Statistics.memory_status(stats.props)
          GUI_Thread.later { update(status) }
      }

    override def addNotify()
    {
      super.addNotify()
      PIDE.session.runtime_statistics += main
    }

    override def removeNotify()
    {
      super.removeNotify()
      PIDE.session.runtime_statistics -= main
    }


    /* mouse listener */

    addMouseListener(new MouseAdapter {
      override def mouseClicked(evt: MouseEvent)
      {
        if (evt.getClickCount == 2) {
          view.getInputHandler.invokeAction("isabelle-monitor-float")
        }
      }
    })
  }

  class Widget_Factory extends StatusWidgetFactory
  {
    override def getWidget(view: View): Widget =
      new Widget { override def getComponent: JComponent = new GUI(view) }
  }
}
