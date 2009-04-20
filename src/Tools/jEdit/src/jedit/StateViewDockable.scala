/*
 * Dockable window with rendered state output
 *
 * @author Fabian Immler, TU Munich
 * @author Johannes Hölzl, TU Munich
 */

package isabelle.jedit


import java.awt.{BorderLayout, Dimension}
import javax.swing.{JButton, JPanel, JScrollPane}

import isabelle.renderer.UserAgent

import org.xhtmlrenderer.simple.{XHTMLPanel, FSScrollPane}
import org.xhtmlrenderer.context.AWTFontResolver
import org.xhtmlrenderer.layout.SharedContext;
import org.xhtmlrenderer.extend.TextRenderer;
import org.xhtmlrenderer.swing.Java2DTextRenderer;

import org.gjt.sp.jedit.jEdit
import org.gjt.sp.jedit.View
import org.gjt.sp.jedit.gui.DockableWindowManager
import org.gjt.sp.jedit.textarea.AntiAlias


class StateViewDockable(view : View, position : String) extends JPanel {

  // outer panel
  if (position == DockableWindowManager.FLOATING)
    setPreferredSize(new Dimension(500, 250))
  setLayout(new BorderLayout)


  // XHTML panel
  val panel = new XHTMLPanel(new UserAgent)


  // anti-aliasing
  // TODO: proper EditBus event handling
  {
    val aa = jEdit.getProperty("view.antiAlias")
    if (aa != null && aa != AntiAlias.NONE) {
      panel.getSharedContext.setTextRenderer(
        {
          val renderer = new Java2DTextRenderer
          renderer.setSmoothingThreshold(0)
          renderer
        })
    }
  }

  
  // copy & paste
  (new SelectionActions).install(panel)


  // scrolling
  add(new FSScrollPane(panel), BorderLayout.CENTER)


  private val fontResolver =
    panel.getSharedContext.getFontResolver.asInstanceOf[AWTFontResolver]
  if (Isabelle.plugin.font != null)
    fontResolver.setFontMapping("Isabelle", Isabelle.plugin.font)

  Isabelle.plugin.font_changed += (font => {
    if (Isabelle.plugin.font != null)
      fontResolver.setFontMapping("Isabelle", Isabelle.plugin.font)

    panel.relayout()
  })

}
