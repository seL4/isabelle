/*
 * ScrollerDockable.scala
 *
 * TODO: clearer seperation of tasks: layout message_view, layout panel (with preferredsize), repaint, relayout, ...
 * + relayout on ValueIsAdjusting while scrolling
 * + scrolling *one* panel 
 */

package isabelle.jedit

import java.io.{ ByteArrayInputStream, FileInputStream, InputStream }

import scala.collection.mutable.ArrayBuffer

import java.awt.{ BorderLayout, GridLayout, Adjustable, Rectangle, Scrollbar }
import java.awt.image.BufferedImage
import java.awt.event.{ AdjustmentListener, AdjustmentEvent, ComponentListener, ComponentEvent }
import javax.swing.{ JScrollBar, JPanel, JScrollPane, ScrollPaneConstants }

import isabelle.IsabelleSystem.getenv

import org.xml.sax.InputSource;

import org.w3c.dom.Document

import org.xhtmlrenderer.simple.XHTMLPanel
import org.xhtmlrenderer.context.AWTFontResolver
import org.xhtmlrenderer.swing.NaiveUserAgent
import org.xhtmlrenderer.resource.CSSResource

import org.gjt.sp.jedit.View

class ScrollerDockable(view : View, position : String) extends JPanel with AdjustmentListener with ComponentListener {
  //holding the unrendered messages
  val message_buffer = new ArrayBuffer[Document]()
  //rendered messages
  var message_cache = Map[Int, XHTMLPanel]()
  // defining the current view
  val scrollunit = 5
  var message_offset = 0 //how many pixels of the lowest message are hidden
  var message_no = -1  //index of the lowest message
  // absolute positioning for messages
  val message_view = new JPanel
  message_view.setLayout(null)
  // setting up view
  setLayout(new BorderLayout())
  val vscroll = new JScrollBar(Adjustable.VERTICAL, 0, 1, 0, 1)
  vscroll.addAdjustmentListener(this)
  add (vscroll, BorderLayout.EAST)
  add (message_view, BorderLayout.CENTER)
  addComponentListener(this)


  //Render a message to a Panel
  def render (message: Document): XHTMLPanel = {
    val panel = new XHTMLPanel(new UserAgent())

    val fontResolver =
      panel.getSharedContext.getFontResolver.asInstanceOf[AWTFontResolver]
    if (Plugin.plugin.viewFont != null)
      fontResolver.setFontMapping("Isabelle", Plugin.plugin.viewFont)

    Plugin.plugin.viewFontChanged.add(font => {
      if (Plugin.plugin.viewFont != null)
        fontResolver.setFontMapping("Isabelle", Plugin.plugin.viewFont)

      panel.relayout()
    })

    panel.setDocument(message, UserAgent.baseURL)
    panel
  }
  
  //calculates preferred size of panel
  def calculate_preferred_size(panel: XHTMLPanel){
    message_view.add (panel)
    panel.setBounds (0, 0, message_view.getWidth, 1) // document has to fit into width
    panel.doLayout (panel.getGraphics) //lay out, preferred size is set then
  }
   
  //render and load a message into cache, place its bottom at y-coordinate;
  def set_message (message_no: Int, y: Int) = {
    //add panel to cache if necessary
    if(!message_cache.isDefinedAt(message_no)){
      if(message_buffer.isDefinedAt(message_no)){
        message_cache = message_cache.update (message_no, render (message_buffer(message_no)))
      }
    }
    val result = message_cache.get(message_no) match {
      case Some(panel) => {
        // recalculate preferred sie after resizing
        if(panel.getPreferredSize.getWidth.toInt != message_view.getWidth)
          calculate_preferred_size (panel)
        //place message on view
        val width = panel.getPreferredSize.getWidth.toInt
        val height = panel.getPreferredSize.getHeight.toInt
        panel.setBounds(0, y - height, width, height)
        message_view.add(panel)
        panel
      }
      case None => null
    }
    result
  }
  
  def move_view (y : Int) = {
    if(message_view.getComponentCount >= 1){
      message_offset += y
      //new panel needed?
      if(message_offset >= message_view.getComponent(0).getHeight)
      {
        //remove bottommost panel
        message_offset -= message_view.getComponent(0).getHeight
        message_no -= 1
        update_view
      } else if (message_offset < 0) {
        //insert panel at the bottom
        message_no += 1
        val panel = set_message (message_no, 0)
        message_offset += panel.getHeight
        update_view
      } else if (message_view.getComponent(message_view.getComponentCount - 1).getY + y > 0){
        //insert panel at the top
        update_view
      } else {
        //move all panels
        message_view.getComponents map (c => {
            val newrect = c.getBounds
            newrect.y = newrect.y + y
            c.setBounds(newrect)
          })
        repaint()
      }
    }
  }
  
  def update_view = {
    message_view.removeAll()
    var n = message_no
    var y:Int = message_view.getHeight + message_offset
    while (y >= 0 && n >= 0){
      val panel = set_message (n, y)
      y = y - panel.getHeight
      n = n - 1
    }
    repaint()
  }

  def add_message (message: Document) = {
    message_buffer += message
    vscroll.setMaximum (Math.max(1, message_buffer.length))
    if(message_no == -1){
      message_no = 0
      update_view
    }
  }
  
  var oldvalue = -1;
  override def adjustmentValueChanged (e : AdjustmentEvent) = {
    //event-handling has to be so general (without UNIT_INCR,...)
    // because all events could be sent as TRACK e.g. on my mac
    val diff = oldvalue - e.getValue
    oldvalue = e.getValue
    if(diff == 1 || diff == -1){
      move_view(diff * scrollunit)
    } else if(diff != 0){
      message_no = e.getValue
      message_offset = 0
      update_view
    }
  }

  // handle Component-Events
  override def componentShown(e: ComponentEvent){}
  override def componentHidden(e: ComponentEvent){}
  override def componentMoved(e: ComponentEvent){}
  override def componentResized(e: ComponentEvent){
    update_view
  }
  
  //register somewhere
  // TODO: only testing atm
  Plugin.plugin.stateUpdate.add(state => {
    var i = 0
    if(state != null) while (i < 500) {
      add_message(state.document)
      i += 1
    }
  })
}


