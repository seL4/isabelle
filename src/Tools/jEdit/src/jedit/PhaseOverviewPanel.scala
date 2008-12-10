/*
 * ErrorOverview.java - Error overview component
 * :tabSize=8:indentSize=8:noTabs=false:
 * :folding=explicit:collapseFolds=1:
 *
 * Copyright (C) 2003 Slava Pestov
 *
 * This program is free software; you can redistribute it and/or
 * modify it under the terms of the GNU General Public License
 * as published by the Free Software Foundation; either version 2
 * of the License, or any later version.
 *
 * This program is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License
 * along with this program; if not, write to the Free Software
 * Foundation, Inc., 59 Temple Place - Suite 330, Boston, MA  02111-1307, USA.
 */

package isabelle.jedit

import isabelle.prover.Command

import javax.swing._
import java.awt.event._
import java.awt._
import org.gjt.sp.jedit.gui.RolloverButton;
import org.gjt.sp.jedit.textarea.JEditTextArea;
import org.gjt.sp.jedit._

class PhaseOverviewPanel(textarea : JEditTextArea) extends JPanel(new BorderLayout) {

  private val WIDTH = 10
	private val HILITE_HEIGHT = 2

  Plugin.plugin.prover.commandInfo.add(_ => repaint())
  setRequestFocusEnabled(false);

  addMouseListener(new MouseAdapter {
    override def mousePressed(evt : MouseEvent) {
      val line = yToLine(evt.getY)
      if(line >= 0 && line < textarea.getLineCount())
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
		if(line >= 0 && line < textarea.getLineCount)
		{
      "TODO: Tooltip"
    } else ""
	}

	override def paintComponent(gfx : Graphics) {
		super.paintComponent(gfx)


		val buffer = textarea.getBuffer

		val line_count = buffer.getLineCount

    for(command <- Plugin.plugin.prover.document.commands) {
      val line1 = buffer.getLineOfOffset(command.start)
      val line2 = buffer.getLineOfOffset(command.stop - 1) + 1
      if(line1 < 0 || line2 > line_count){
        System.err.println("invalid line numbers: " + line1 + " - " + line2)
      } else {
        val y1 = lineToY(line1)
        val y2 = lineToY(line2) - 1
        val linelength = buffer.getLineLength(line1)
        val color = command.phase match {
          case Command.Phase.UNPROCESSED => Color.yellow
          case Command.Phase.FINISHED => Color.green
          case Command.Phase.FAILED => Color.red
        }
				gfx.setColor(color)
				gfx.fillRect(0, y1, getWidth, 1 max y2 - y1)
			}
		}
	}

	override def getPreferredSize : Dimension =
	{
		new Dimension(10,0)
	}


	private def lineToY(line : Int) : Int =
	{
		(line * getHeight) / textarea.getBuffer.getLineCount
	}

	private def yToLine(y : Int) : Int =
	{
		(y * textarea.getBuffer.getLineCount) / getHeight
	}

}