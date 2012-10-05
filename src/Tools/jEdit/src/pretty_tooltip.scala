/*  Title:      Tools/jEdit/src/pretty_tooltip.scala
    Author:     Makarius

Enhanced tooltip window based on Pretty_Text_Area.
*/

package isabelle.jedit


import isabelle._

import java.awt.{Color, Point, BorderLayout}
import java.awt.event.{ActionListener, ActionEvent, KeyEvent, WindowEvent, WindowAdapter}
import javax.swing.{SwingUtilities, JWindow, JPanel, JComponent, KeyStroke}
import javax.swing.border.LineBorder

import org.gjt.sp.jedit.View
import org.gjt.sp.jedit.textarea.TextArea


class Pretty_Tooltip(
  view: View,
  text_area: TextArea,
  rendering: Isabelle_Rendering,
  x: Int, y: Int, body: XML.Body) extends JWindow(view)
{
  window =>

  private val point = {
    val painter = text_area.getPainter
    val fm = painter.getFontMetrics
    val bounds = painter.getBounds()
    val point = new Point(bounds.x + x, bounds.y + fm.getHeight + y)
    SwingUtilities.convertPointToScreen(point, painter)
    point
  }

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
  window.setLocation(point.x, point.y)
  window.setSize(pretty_text_area.getPainter.getFontMetrics.charWidth(Pretty.spc) *
    Isabelle.options.int("jedit_tooltip_margin"), 100)

  window.setVisible(true)
  pretty_text_area.refresh()
}

