/*
 * ScrollerDockable.scala
 *
 * TODO: clearer seperation of tasks: layout message_view, layout panel (with preferredsize), repaint, relayout, ...
 * + relayout on ValueIsAdjusting while scrolling
 * + scrolling *one* panel 
 */

package isabelle.jedit

import scala.collection.mutable.ArrayBuffer

import java.awt.{ BorderLayout, Adjustable }
import java.awt.event.{ ActionListener, ActionEvent, AdjustmentListener, AdjustmentEvent, ComponentListener, ComponentEvent }
import javax.swing.{ JPanel, JRadioButton, JScrollBar, JTextArea, Timer }

import org.w3c.dom.Document

import org.xhtmlrenderer.simple.XHTMLPanel
import org.xhtmlrenderer.context.AWTFontResolver

import org.gjt.sp.jedit.View

class ScrollerDockable(view : View, position : String) extends JPanel with AdjustmentListener with ComponentListener {
  //holding the unrendered messages
  val message_buffer = new ArrayBuffer[Document]()
  //rendered messages
  var message_cache = Map[Int, XHTMLPanel]()
  // defining the current view
  val scrollunit = 1
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
  //automated scrolling, new message ind
  val infopanel = new JPanel
  val auto_scroll = new JRadioButton("Auto Scroll", false)
  val new_message_ind = new JTextArea("0")
  infopanel.add(new_message_ind)
  infopanel.add(auto_scroll)
  add (infopanel, BorderLayout.SOUTH)

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
  
  // panel has to be displayable in container message_view for doLayout to have
  // an effect, especially returning correct preferredSize
  def calculate_preferred_size(panel: XHTMLPanel){
    message_view.add (panel)
    panel.setBounds (0, 0, message_view.getWidth, 1) // document has to fit into width
    panel.doLayout (panel.getGraphics) //lay out, preferred size is set then
    // if there are thousands of empty panels, all have to be rendered -
    // but this takes time (even for empty panels); therefore minimum size
    panel.setPreferredSize(new java.awt.Dimension(message_view.getWidth,Math.max(50, panel.getPreferredSize.getHeight.toInt)))
  }
   
  //render and load a message into cache, place its bottom at y-coordinate;
  def set_message (message_no: Int, y: Int) = {
    //add panel to cache if necessary and possible
    if(!message_cache.isDefinedAt(message_no) && message_buffer.isDefinedAt(message_no)){
      message_cache = message_cache.update (message_no, render (message_buffer(message_no)))
    }
    val result = message_cache.get(message_no) match {
      case Some(panel) => {
        // recalculate preferred size after resizing the message_view
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

  //move view a given amount of pixels
  // attention: y should be small, because messages are rendered incremental
  // (no knowledge on height of messages)
  def move_view (y : Int) = {
    var update = false
    if(message_view.getComponentCount >= 1){
      message_offset += y
      //remove bottommost panels
      while (message_offset >= message_view.getComponent(0).getHeight)
      {
        message_offset -= message_view.getComponent(0).getHeight
        message_no -= 1
        update_view
        update = true
      }
      //insert panels at the bottom
      while (message_offset < 0) {
        message_no += 1
        val panel = set_message (message_no, 0)
        message_offset += panel.getHeight
        update_view
        update = true
     }
      //insert panel at the top
      if (message_view.getComponent(message_view.getComponentCount - 1).getY + y > 0){
        update_view
        update = true
      }
      //simply move panels
      if(!update){
        message_view.getComponents map (c => {
            val newrect = c.getBounds
            newrect.y = newrect.y + y
            c.setBounds(newrect)
          })
        repaint()
      } else {
        vscroll.setValue(message_no)
      }
    }
  }
  
  def update_view = {
    message_view.removeAll()
    var n = message_no
    var y:Int = message_view.getHeight + message_offset
    while (y >= 0 && n >= 0){
      val panel = set_message (n, y)
      panel.setBorder(javax.swing.border.LineBorder.createBlackLineBorder)
      y = y - panel.getHeight
      n = n - 1
    }
    repaint()
  }

  val scroll_delay_timer : Timer = new Timer(300, new ActionListener {
      override def actionPerformed(e:ActionEvent){
        //fire scroll-event => updating is done by scroll-event-handling
        if(message_no != message_buffer.size) vscroll.setValue(message_buffer.size - 1)
        scroll_delay_timer.stop
      }
    })

  def add_message (message: Document) = {
    message_buffer += message
    vscroll.setMaximum (Math.max(1, message_buffer.length))
    if(message_no == -1 || auto_scroll.isSelected){
      if (! scroll_delay_timer.isRunning()){
        vscroll.setValue(message_buffer.size - 1)
        scroll_delay_timer.start()
      }
    }
  }
  
  override def adjustmentValueChanged (e : AdjustmentEvent) = {
    //event-handling has to be so general (without UNIT_INCR,...)
    // because all events could be sent as TRACK e.g. on my mac
    if (e.getSource == vscroll){
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


