package isabelle.jedit


import java.awt.BorderLayout
import javax.swing.{ JButton, JPanel, JScrollPane }

import isabelle.IsabelleSystem.getenv

import org.xhtmlrenderer.simple.XHTMLPanel
import org.xhtmlrenderer.context.AWTFontResolver

import org.gjt.sp.jedit.View

class StateViewDockable(view : View, position : String) extends JPanel {
  val panel = new XHTMLPanel(new UserAgent())
  setLayout(new BorderLayout)

  //Copy-paste-support
  private val cp = new SelectionActions
  cp.install(panel)

  add(new JScrollPane(panel), BorderLayout.CENTER)

  private val fontResolver =
    panel.getSharedContext.getFontResolver.asInstanceOf[AWTFontResolver]
  if (Plugin.plugin.viewFont != null)
    fontResolver.setFontMapping("Isabelle", Plugin.plugin.viewFont)

  Plugin.plugin.viewFontChanged.add(font => {
    if (Plugin.plugin.viewFont != null)
      fontResolver.setFontMapping("Isabelle", Plugin.plugin.viewFont)

    panel.relayout()
  })

}
