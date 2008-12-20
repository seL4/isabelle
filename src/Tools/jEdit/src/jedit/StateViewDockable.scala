/*
 * Dockable window with rendered state output
 *
 * @author Fabian Immler, TU Munich
 * @author Johannes Hölzl, TU Munich
 */

package isabelle.jedit


import java.awt.{BorderLayout, Dimension}
import javax.swing.{JButton, JPanel, JScrollPane}

import isabelle.IsabelleSystem.getenv

import org.xhtmlrenderer.simple.XHTMLPanel
import org.xhtmlrenderer.context.AWTFontResolver

import org.gjt.sp.jedit.View
import org.gjt.sp.jedit.gui.DockableWindowManager


class StateViewDockable(view : View, position : String) extends JPanel {
  val panel = new XHTMLPanel(new UserAgent())

  if (position == DockableWindowManager.FLOATING)
    setPreferredSize(new Dimension(500, 250))

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
