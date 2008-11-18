/*
 * SelectionActions.scala
 *
 * To change this template, choose Tools | Template Manager
 * and open the template in the editor.
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
      val encoded = VFS.converter.encode (selected_string)
      mousePressed(new java.awt.event.MouseEvent(getComponent,0,0,0,0,0,0, false))
      mouseReleased(new java.awt.event.MouseEvent(getComponent,0,0,0,0,0,0, false))
      val clipboard = java.awt.Toolkit.getDefaultToolkit().getSystemClipboard;
      val transferable = new java.awt.datatransfer.StringSelection(encoded)
      clipboard.setContents(transferable, null)
      super.install(getComponent)
  }
  
  override def keyPressed (e: KeyEvent) {
    if(e.getKeyCode == KeyEvent.VK_ENTER) {
      copyaction
      e.consume
    }
  }
  override def keyReleased (e: KeyEvent) {
    
  }
  override def keyTyped (e: KeyEvent) {
    
  }


}
