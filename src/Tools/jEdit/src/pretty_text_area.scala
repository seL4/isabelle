/*  Title:      Tools/jEdit/src/pretty_text_area.scala
    Author:     Makarius

GUI component for pretty-printed with markup, rendered like jEdit text area.
*/

package isabelle.jedit


import isabelle._

import java.awt.{Font, FontMetrics}
import org.gjt.sp.jedit.textarea.{AntiAlias, JEditEmbeddedTextArea}
import org.gjt.sp.jedit.jEdit
import org.gjt.sp.util.SyntaxUtilities
import scala.swing.{BorderPanel, Component}


class Pretty_Text_Area extends BorderPanel
{
  Swing_Thread.require()

  val text_area = new JEditEmbeddedTextArea

  private var current_font_metrics: FontMetrics = null
  private var current_font_family = "Dialog"
  private var current_font_size: Int = 12
  private var current_margin: Int = 0
  private var current_body: XML.Body = Nil

  def refresh()
  {
    Swing_Thread.require()

    val font = new Font(current_font_family, Font.PLAIN, current_font_size)

    val painter = text_area.getPainter
    painter.setFont(font)
    painter.setAntiAlias(new AntiAlias(jEdit.getProperty("view.antiAlias")))
    painter.setStyles(SyntaxUtilities.loadStyles(current_font_family, current_font_size))

    current_font_metrics = painter.getFontMetrics(font)
    current_margin = (size.width / (current_font_metrics.charWidth(Pretty.spc) max 1) - 4) max 20

    val text =
      Pretty.string_of(current_body, current_margin, Pretty.font_metric(current_font_metrics))

    val buffer = text_area.getBuffer
    try {
      buffer.beginCompoundEdit
      text_area.setText(text)
      text_area.setCaretPosition(0)
    }
    finally {
      buffer.endCompoundEdit
    }
  }

  def resize(font_family: String, font_size: Int)
  {
    Swing_Thread.require()

    current_font_family = font_family
    current_font_size = font_size
    refresh()
  }

  def update(body: XML.Body)
  {
    Swing_Thread.require()

    current_body = body
    refresh()
  }

  layout(Component.wrap(text_area)) = BorderPanel.Position.Center
}

