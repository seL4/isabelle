/*
 * Information on command status left of scrollbar (with panel)
 *
 * @author Fabian Immler, TU Munich
 */

package isabelle.jedit


import isabelle.proofdocument.{Command, Proof_Document, Theory_View}

import javax.swing.{JPanel, ToolTipManager}
import java.awt.event.{MouseAdapter, MouseEvent}
import java.awt.{BorderLayout, Graphics, Dimension}

import org.gjt.sp.jedit.gui.RolloverButton
import org.gjt.sp.jedit.textarea.JEditTextArea


class Document_Overview(
    text_area: JEditTextArea,
    to_current: (Proof_Document, Int) => Int)
  extends JPanel(new BorderLayout)
{
  private val WIDTH = 10
  private val HEIGHT = 2

  setRequestFocusEnabled(false)

  addMouseListener(new MouseAdapter {
    override def mousePressed(event: MouseEvent) {
      val line = y_to_line(event.getY)
      if (line >= 0 && line < text_area.getLineCount)
        text_area.setCaretPosition(text_area.getLineStartOffset(line))
    }
  })

  override def addNotify() {
    super.addNotify()
    ToolTipManager.sharedInstance.registerComponent(this)
  }

  override def removeNotify() {
    super.removeNotify
    ToolTipManager.sharedInstance.unregisterComponent(this)
  }

  override def getToolTipText(event: MouseEvent): String =
  {
    val buffer = text_area.getBuffer
    val lineCount = buffer.getLineCount
    val line = y_to_line(event.getY())
    if (line >= 0 && line < text_area.getLineCount) "<html><b>TODO:</b><br>Tooltip</html>"
    else ""
  }

  override def paintComponent(gfx: Graphics)
  {
    super.paintComponent(gfx)
    val buffer = text_area.getBuffer
    val theory_view = Isabelle.plugin.theory_view(buffer).get
    val doc = theory_view.current_document()

    for (command <- doc.commands) {
      val line1 = buffer.getLineOfOffset(to_current(doc, command.start(doc)))
      val line2 = buffer.getLineOfOffset(to_current(doc, command.stop(doc))) + 1
      val y = line_to_y(line1)
      val height = HEIGHT * (line2 - line1)
      gfx.setColor(Theory_View.choose_color(command, doc))
      gfx.fillRect(0, y, getWidth - 1, height)
    }
  }

  override def getPreferredSize = new Dimension(WIDTH, 0)

  private def line_to_y(line: Int): Int =
    (line * getHeight) / (text_area.getBuffer.getLineCount max text_area.getVisibleLines)

  private def y_to_line(y: Int): Int =
    (y * (text_area.getBuffer.getLineCount max text_area.getVisibleLines)) / getHeight
}