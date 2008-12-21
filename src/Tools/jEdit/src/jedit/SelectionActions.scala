/*
 * Text selection for XHTML renderer
 *
 * @author Fabian Immler, TU Munich
 */

package isabelle.jedit

import org.w3c.dom.ranges.Range
import org.w3c.dom.DocumentFragment
import org.xhtmlrenderer.swing.SelectionHighlighter
import org.xhtmlrenderer.simple.XHTMLPanel

import java.awt.event.{KeyListener, KeyEvent}

import org.gjt.sp.jedit.gui._

class SelectionActions extends SelectionHighlighter with KeyListener{

  override def install(panel: XHTMLPanel) {
    super.install(panel)
    panel.addKeyListener(this)
  }
  

  def copyaction {
      val selected_string = getSelectionRange.toString
      val encoded = Plugin.self.symbols.encode(selected_string)
      val clipboard = java.awt.Toolkit.getDefaultToolkit().getSystemClipboard;
      val transferable = new java.awt.datatransfer.StringSelection(selected_string)
      clipboard.setContents(transferable, null)
  }
  
  override def keyPressed(e: KeyEvent) {
    if(e.getKeyCode == KeyEvent.VK_ENTER) {
      copyaction
      e.consume
    }
  }
  
  override def keyReleased(e: KeyEvent) {
  }

  override def keyTyped(e: KeyEvent) {
  }
}
