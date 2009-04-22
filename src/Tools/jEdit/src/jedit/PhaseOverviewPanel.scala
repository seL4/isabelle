/*
 * Information on command status left of scrollbar (with panel)
 *
 * @author Fabian Immler, TU Munich
 */

package isabelle.jedit

import isabelle.prover.Command
import isabelle.proofdocument.ProofDocument
import isabelle.utils.Delay

import javax.swing._
import java.awt.event._
import java.awt._
import org.gjt.sp.jedit.gui.RolloverButton;
import org.gjt.sp.jedit.textarea.JEditTextArea;
import org.gjt.sp.jedit.buffer.JEditBuffer;
import org.gjt.sp.jedit._

class PhaseOverviewPanel(prover: isabelle.prover.Prover, to_current: (String, Int) => Int) extends JPanel(new BorderLayout) {

  private val WIDTH = 10
	private val HILITE_HEIGHT = 2
  var textarea : JEditTextArea = null

  val repaint_delay = new isabelle.utils.Delay(100, () => repaint())

  setRequestFocusEnabled(false);

  addMouseListener(new MouseAdapter {
    override def mousePressed(evt : MouseEvent) {
      val line = yToLine(evt.getY)
      if (line >= 0 && line < textarea.getLineCount())
        textarea.setCaretPosition(textarea.getLineStartOffset(line))
    }
  })

	override def addNotify	{
		super.addNotify();
		ToolTipManager.sharedInstance.registerComponent(this);
	}

	override def removeNotify()
	{
		super.removeNotify
		ToolTipManager.sharedInstance.unregisterComponent(this);
	}

	override def getToolTipText(evt : MouseEvent) : String =
	{
		val buffer = textarea.getBuffer
		val lineCount = buffer.getLineCount
		val line = yToLine(evt.getY())
		if (line >= 0 && line < textarea.getLineCount)
		{
      "TODO: Tooltip"
    } else ""
	}

  private def paintCommand(command : Command, buffer : JEditBuffer, doc: ProofDocument, gfx : Graphics) {
    val line1 = buffer.getLineOfOffset(to_current(doc.id, command.start(doc)))
    val line2 = buffer.getLineOfOffset(to_current(doc.id, command.stop(doc) - 1)) + 1
    val y = lineToY(line1)
    val height = lineToY(line2) - y - 1
    val (light, dark) = command.status match {
      case Command.Status.UNPROCESSED => (Color.yellow, new Color(128,128,0))
      case Command.Status.FINISHED => (Color.green, new Color(0, 128, 0))
      case Command.Status.FAILED => (Color.red, new Color(128,0,0))
    }

    gfx.setColor(light)
    gfx.fillRect(0, y, getWidth - 1, 1 max height)
    if (height > 2) {
      gfx.setColor(dark)
      gfx.drawRect(0, y, getWidth - 1, height)
    }
  }

	override def paintComponent(gfx : Graphics) {
		super.paintComponent(gfx)

		val buffer = textarea.getBuffer
    val document = prover.document
    for (c <- document.commands)
      paintCommand(c, buffer, document, gfx)

	}

	override def getPreferredSize = new Dimension(10,0)

	private def lineToY(line : Int) : Int =
		(line * getHeight) / (textarea.getBuffer.getLineCount max textarea.getVisibleLines)

	private def yToLine(y : Int) : Int =
		(y * (textarea.getBuffer.getLineCount max textarea.getVisibleLines)) / getHeight

}