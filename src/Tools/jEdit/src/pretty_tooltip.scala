/*  Title:      Tools/jEdit/src/pretty_tooltip.scala
    Author:     Makarius

Enhanced tooltip window based on Pretty_Text_Area.
*/

package isabelle.jedit


import isabelle._

import java.awt.{Toolkit, Color, Point, BorderLayout}
import java.awt.event.{ActionListener, ActionEvent, KeyEvent, WindowEvent, WindowAdapter}
import javax.swing.{SwingUtilities, JWindow, JPanel, JComponent, KeyStroke}
import javax.swing.border.LineBorder

import org.gjt.sp.jedit.View
import org.gjt.sp.jedit.textarea.TextArea


class Pretty_Tooltip(
  view: View,
  text_area: TextArea,
  rendering: Isabelle_Rendering,
  mouse_x: Int, mouse_y: Int, body: XML.Body) extends JWindow(view)
{
  window =>

  window.addWindowFocusListener(new WindowAdapter {
    override def windowLostFocus(e: WindowEvent) { window.dispose() }
  })

  window.setContentPane(new JPanel(new BorderLayout) {
    private val action_listener = new ActionListener {
      def actionPerformed(e: ActionEvent) {
        e.getActionCommand match {
          case "close" => window.dispose()
          case _ =>
        }
      }
    }
    registerKeyboardAction(action_listener, "close",
      KeyStroke.getKeyStroke(KeyEvent.VK_ESCAPE, 0), JComponent.WHEN_FOCUSED)

    override def getFocusTraversalKeysEnabled(): Boolean = false
  })
  window.getRootPane.setBorder(new LineBorder(Color.BLACK))

  val pretty_text_area = new Pretty_Text_Area(view)
  pretty_text_area.getPainter.setBackground(rendering.tooltip_color)
  pretty_text_area.resize(
    Isabelle.font_family(), Isabelle.font_size("jedit_tooltip_font_scale").round)
  pretty_text_area.update(rendering.snapshot, body)

  window.add(pretty_text_area)

  {
    val font_metrics = pretty_text_area.getPainter.getFontMetrics
    val margin = Isabelle.options.int("jedit_tooltip_margin")  // FIXME via rendering?!
    val lines =  // FIXME avoid redundant formatting
      XML.traverse_text(Pretty.formatted(body, margin, Pretty.font_metric(font_metrics)))(0)(
        (n: Int, s: String) => n + s.iterator.filter(_ == '\n').length)

    val screen = Toolkit.getDefaultToolkit.getScreenSize
    val w = (font_metrics.charWidth(Pretty.spc) * margin) min (screen.width / 2)
    val h = (font_metrics.getHeight * (lines + 2)) min (screen.height / 2)
    window.setSize(w, h)
  }

  {
    val container = text_area.getPainter
    val font_metrics = container.getFontMetrics
    val point = new Point(mouse_x, mouse_y + font_metrics.getHeight / 2)
    SwingUtilities.convertPointToScreen(point, container)

    val screen = Toolkit.getDefaultToolkit.getScreenSize
    val x = point.x min (screen.width - window.getWidth)
    val y = point.y min (screen.height - window.getHeight)
    window.setLocation(x, y)
  }

  window.setVisible(true)
  pretty_text_area.refresh()  // FIXME avoid redundant formatting
}

