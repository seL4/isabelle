/*
 * Dockable window with scrollable messages
 *
 * @author Fabian Immler, TU Munich
 */

package isabelle.jedit


import isabelle.Isabelle_Process.Result
import isabelle.renderer.UserAgent


import scala.collection.mutable

import java.awt.{BorderLayout, Adjustable, Dimension}
import java.awt.event.{ActionListener, ActionEvent, AdjustmentListener, AdjustmentEvent, ComponentListener, ComponentEvent}
import javax.swing.{JFrame, JPanel, JRadioButton, JScrollBar, JTextArea, Timer}

import org.w3c.dom.Document

import org.xhtmlrenderer.simple.XHTMLPanel
import org.xhtmlrenderer.context.AWTFontResolver

import org.gjt.sp.jedit.View
import org.gjt.sp.jedit.gui.DockableWindowManager


trait Renderer[U, R] {
  def render (u: U): R
  //relayout a rendered element using argument a
  def relayout (r: R, a: Int)
}

trait Unrendered[U] {
  def addUnrendered (id: Int, u: U) : Unit
  def getUnrendered (id: Int) : Option[U]
  def size : Int
}

trait Rendered[U, R] {
  def getRendered (id: Int) : Option[R]
  val renderer : Renderer[U, R]
}

class MessagePanel(cache: Rendered[_, XHTMLPanel]) extends JPanel {
  // defining the current view
  var offset = 0 //what percentage of the lowest message is hidden
  var no = -1  //index of the lowest message

  // preferences
  val scrollunit = 5
  setLayout(null)
  
  // place the bottom of the message at y-coordinate and return the rendered panel
  def place_message (message_no: Int, y: Int) = {
    //add panel to cache if necessary and possible
    cache.getRendered(message_no) match {
      case Some(panel) => {
        //panel has to be displayable before calculating preferred size!
        add(panel)
        // recalculate preferred size after resizing the message_view
        if (panel.getPreferredSize.getWidth.toInt != getWidth) {
          cache.renderer.relayout (panel, getWidth)
        }
        val width = panel.getPreferredSize.getWidth.toInt
        val height = panel.getPreferredSize.getHeight.toInt
        panel.setBounds(0, y - height, width, height)
        panel
      }
      case None => null
    }
  }
  
  override def doLayout = {
    removeAll()
    //calculate offset in pixel
    val panel = place_message(no, 0)
    val pixeloffset = if (panel != null) panel.getHeight*offset/100 else 0
    var n = no
    var y:Int = getHeight + pixeloffset
    while (y >= 0 && n >= 0) {
      val panel = place_message (n, y)
      if (panel != null) {
        panel.setBorder(javax.swing.border.LineBorder.createBlackLineBorder)
        y = y - panel.getHeight
      }
      n = n - 1
    }
  }  
}

class InfoPanel extends JPanel {
  val auto_scroll = new JRadioButton("Auto Scroll", false)
  val message_ind = new JTextArea("0")
  add(message_ind)
  add(auto_scroll)
  
  def isAutoScroll = auto_scroll.isSelected
  def setIndicator(b: Boolean) = {
    message_ind.setBackground(if (b) java.awt.Color.red else java.awt.Color.white)
  }
  def setText(s: String) {
    message_ind.setText(s)
  }
}


class ScrollerDockable(view : View, position : String) extends JPanel with AdjustmentListener {

  val renderer:Renderer[Result, XHTMLPanel] = new ResultToPanelRenderer
  val buffer:Unrendered[Result] = new MessageBuffer
  val cache:Rendered[Result, XHTMLPanel] = new PanelCache(buffer, renderer)

  val subunits = 100
  // set up view
  val message_panel = new MessagePanel(cache)
  val infopanel = new InfoPanel
  val vscroll = new JScrollBar(Adjustable.VERTICAL, 0, 1, 0, 1)
  vscroll.setUnitIncrement(subunits / 3)
  vscroll.setBlockIncrement(subunits)
  vscroll.addAdjustmentListener(this)

  if (position == DockableWindowManager.FLOATING)
    setPreferredSize(new Dimension(500, 250))

  setLayout(new BorderLayout())
  add (vscroll, BorderLayout.EAST)
  add (message_panel, BorderLayout.CENTER)
  add (infopanel, BorderLayout.SOUTH)
  
  // do not show every new message, wait a certain amount of time
  val message_ind_timer : Timer = new Timer(250, new ActionListener {
      // this method is called to indicate a new message
      override def actionPerformed(e:ActionEvent) {
        //fire scroll-event if necessary and wanted
        if (message_panel.no != buffer.size*subunits - 1 && infopanel.isAutoScroll) {
          vscroll.setValue(buffer.size*subunits - 1)
        }
        infopanel.setIndicator(false)
      }
    })

  def add_result(result: Result) {
    buffer.addUnrendered(buffer.size, result)
    vscroll.setMaximum ((buffer.size * subunits) max 1)
    infopanel.setIndicator(true)
    infopanel.setText(buffer.size.toString)

    if (!message_ind_timer.isRunning()) {
      if (infopanel.isAutoScroll) {
        vscroll.setValue(buffer.size*subunits - 1)
      }
      message_ind_timer.setRepeats(false)
      message_ind_timer.start()
    }

    if (message_panel.no == -1) {
      message_panel.no = 0
      message_panel.revalidate
    }
  }

  override def adjustmentValueChanged (e : AdjustmentEvent) = {
    //event-handling has to be so general (without UNIT_INCR,...)
    // because all events could be sent as TRACK e.g. on my mac
    if (e.getSource == vscroll) {
      message_panel.no = e.getValue / subunits
      message_panel.offset = 100 - 100 * (e.getValue % subunits) / subunits
      message_panel.revalidate
    }
  }

  
  // TODO: register
  //Isabelle.plugin.prover.allInfo.add(add_result(_))
}

//Concrete Implementations

//containing the unrendered messages
class MessageBuffer extends mutable.HashMap[Int,Result] with Unrendered[Result]{
  override def addUnrendered (id: Int, m: Result) {
    update(id, m)
  }
  override def getUnrendered(id: Int): Option[Result] = {
    if (id < size && id >= 0 && apply(id) != null) Some (apply(id))
    else None
  }
  override def size = super.size
}

//containing the rendered messages
class PanelCache (buffer: Unrendered[Result], val renderer: Renderer[Result, XHTMLPanel])
  extends mutable.HashMap[Int, XHTMLPanel] with Rendered[Result, XHTMLPanel]{

  override def getRendered (id: Int): Option[XHTMLPanel] = {
    //get message from buffer and render it if necessary
    if (!isDefinedAt(id)) {
      buffer.getUnrendered(id) match {
        case Some (message) =>
          update (id, renderer.render (message))
        case None =>
      }
    }
    val result = try {
      Some(apply(id))
    } catch {
      case _ => {
          None
      }
    }
    return result
  }
}

class ResultToPanelRenderer extends Renderer[Result, XHTMLPanel]{
  
  def render (r: Result): XHTMLPanel = {
    val panel = new XHTMLPanel(new UserAgent())
    val fontResolver =
      panel.getSharedContext.getFontResolver.asInstanceOf[AWTFontResolver]
    if (Isabelle.plugin.font != null)
      fontResolver.setFontMapping("Isabelle", Isabelle.plugin.font)

    Isabelle.plugin.font_changed += (font => {
      if (Isabelle.plugin.font != null)
        fontResolver.setFontMapping("Isabelle", Isabelle.plugin.font)
      panel.relayout()
    })
    val document = XML.document(Isabelle_Process.parse_message(Isabelle.system, r))
    panel.setDocument(document, UserAgent.base_URL)
    val sa = new SelectionActions
    sa.install(panel)
    panel
  }
  
  def relayout (panel: XHTMLPanel, width : Int) {
    // ATTENTION:
    // panel has to be displayable in a frame/container message_view for doDocumentLayout to have
    // an effect, especially returning correct preferredSize
    panel.setBounds (0, 0, width, 1) // document has to fit into width
    panel.doDocumentLayout (panel.getGraphics) //lay out, preferred size is set then
    // if there are thousands of empty panels, all have to be rendered -
    // but this takes time (even for empty panels); therefore minimum size
    panel.setPreferredSize(new java.awt.Dimension(width, Math.max(25, panel.getPreferredSize.getHeight.toInt)))
  }

}