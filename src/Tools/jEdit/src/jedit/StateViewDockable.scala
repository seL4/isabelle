package isabelle.jedit


import java.awt.BorderLayout
import javax.swing.{ JButton, JPanel, JScrollPane }

import isabelle.IsabelleSystem.getenv

import org.w3c.dom.Document

import org.xhtmlrenderer.simple.XHTMLPanel
import org.xhtmlrenderer.context.AWTFontResolver

import org.gjt.sp.jedit.View

class StateViewDockable(view : View, position : String) extends JPanel {
  {
    val panel = new XHTMLPanel(new UserAgent())
    setLayout(new BorderLayout)

    //Copy-paste-support
    val cp = new SelectionActions
    cp.install(panel)

    add(new JScrollPane(panel), BorderLayout.CENTER)
    
    val fontResolver =
      panel.getSharedContext.getFontResolver.asInstanceOf[AWTFontResolver]
    if (Plugin.plugin.viewFont != null)
      fontResolver.setFontMapping("Isabelle", Plugin.plugin.viewFont)

    Plugin.plugin.viewFontChanged.add(font => {
      if (Plugin.plugin.viewFont != null)
        fontResolver.setFontMapping("Isabelle", Plugin.plugin.viewFont)
      
      panel.relayout()
    })
    
    Plugin.plugin.stateUpdate.add(state => {
      if (state == null)
        panel.setDocument(null : Document)
      else
        panel.setDocument(state.results_xml, UserAgent.baseURL)
    })
  }
}
