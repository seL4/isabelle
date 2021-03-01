/*  Title:      Tools/jEdit/src/status_widget.scala
    Author:     Makarius

ML status bar: heap and garbage collection.
*/

package isabelle.jedit


import isabelle._
import java.awt.{Color, Dimension, Graphics, Graphics2D, Insets, RenderingHints}
import java.awt.font.FontRenderContext
import java.awt.event.{ActionEvent, ActionListener, MouseAdapter, MouseEvent}

import javax.swing.{JComponent, JLabel, Timer}
import org.gjt.sp.jedit.{View, jEdit}
import org.gjt.sp.jedit.gui.statusbar.{StatusWidgetFactory, Widget}


object Status_Widget
{
  /** generic GUI **/

  private val template = "ABC: 99999/99999MB"

  abstract class GUI(view: View) extends JComponent
  {
    /* init */

    setFont(new JLabel().getFont)

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

    def get_status: (String, Double)

    override def paintComponent(gfx: Graphics): Unit =
    {
      super.paintComponent(gfx)

      val insets = new Insets(0, 0, 0, 0)

      val width = getWidth - insets.left - insets.right
      val height = getHeight - insets.top - insets.bottom - 1

      val (text, fraction) = get_status
      val width2 = (width * fraction).toInt

      val text_bounds = gfx.getFont.getStringBounds(text, font_render_context)
      val text_x = insets.left + ((width - text_bounds.getWidth).toInt / 2)
      val text_y = (insets.top + line_metrics.getAscent).toInt

      gfx.asInstanceOf[Graphics2D].
        setRenderingHint(
          RenderingHints.KEY_TEXT_ANTIALIASING,
          RenderingHints.VALUE_TEXT_ANTIALIAS_ON)

      gfx.setColor(progress_background)
      gfx.fillRect(insets.left, insets.top, width2, height)

      gfx.setColor(progress_foreground)
      gfx.setClip(insets.left, insets.top, width2, height)
      gfx.drawString(text, text_x, text_y)

      gfx.setColor(getForeground)
      gfx.setClip(insets.left + width2, insets.top, getWidth - insets.left - width2, height)
      gfx.drawString(text, text_x, text_y)
    }


    /* mouse listener */

    def action: String

    addMouseListener(new MouseAdapter {
      override def mouseClicked(evt: MouseEvent): Unit =
      {
        if (evt.getClickCount == 2) {
          view.getInputHandler.invokeAction(action)
        }
      }
    })
  }



  /** Java **/

  class Java_GUI(view: View) extends GUI(view)
  {
    /* component state -- owned by GUI thread */

    private var status = Java_Statistics.memory_status()

    def get_status: (String, Double) =
    {
      ("JVM: " + (status.heap_used / 1024 / 1024) + "/" + (status.heap_size / 1024 / 1024) + "MB",
        status.heap_used_fraction)
    }

    private def update_status(new_status: Java_Statistics.Memory_Status): Unit =
    {
      if (status != new_status) {
        status = new_status
        repaint()
      }
    }


    /* timer */

    private val timer =
      new Timer(500, new ActionListener {
        override def actionPerformed(e: ActionEvent): Unit =
          update_status(Java_Statistics.memory_status())
      })

    override def addNotify(): Unit =
    {
      super.addNotify()
      timer.start()
    }

    override def removeNotify(): Unit =
    {
      super.removeNotify()
      timer.stop()
    }


    /* action */

    setToolTipText("Java heap memory (double-click for monitor application)")

    override def action: String = "isabelle.java-monitor"
  }

  class Java_Factory extends StatusWidgetFactory
  {
    override def getWidget(view: View): Widget =
      new Widget { override def getComponent: JComponent = new Java_GUI(view) }
  }



  /** ML **/

  class ML_GUI(view: View) extends GUI(view)
  {
    /* component state -- owned by GUI thread */

    private var status = ML_Statistics.memory_status(Nil)

    def get_status: (String, Double) =
      status.gc_progress match {
        case Some(p) => ("ML cleanup", 1.0 - p)
        case None =>
          ("ML: " + (status.heap_used / 1024 / 1024) + "/" + (status.heap_size / 1024 / 1024) + "MB",
            status.heap_used_fraction)
      }

    private def update_status(new_status: ML_Statistics.Memory_Status): Unit =
    {
      if (status != new_status) {
        status = new_status
        repaint()
      }
    }


    /* main */

    private val main =
      Session.Consumer[Session.Runtime_Statistics](getClass.getName) {
        case stats =>
          val status = ML_Statistics.memory_status(stats.props)
          GUI_Thread.later { update_status(status) }
      }

    override def addNotify(): Unit =
    {
      super.addNotify()
      PIDE.session.runtime_statistics += main
    }

    override def removeNotify(): Unit =
    {
      super.removeNotify()
      PIDE.session.runtime_statistics -= main
    }


    /* action */

    setToolTipText("ML heap memory (double-click for monitor panel)")

    override def action: String = "isabelle-monitor-float"
  }

  class ML_Factory extends StatusWidgetFactory
  {
    override def getWidget(view: View): Widget =
      new Widget { override def getComponent: JComponent = new ML_GUI(view) }
  }
}
