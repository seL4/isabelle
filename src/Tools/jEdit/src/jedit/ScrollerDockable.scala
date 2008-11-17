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
  val message_panel = new JPanel
  message_panel.setLayout(null)
  // setting up view
  setLayout(new BorderLayout())
  val vscroll = new JScrollBar(Adjustable.VERTICAL, 0, 1, 0, 1)
  vscroll.addAdjustmentListener(this)
  add (vscroll, BorderLayout.EAST)
  add (message_panel, BorderLayout.CENTER)
  addComponentListener(this)
  //automated scrolling, new message ind
  val infopanel = new JPanel
  val auto_scroll = new JRadioButton("Auto Scroll", false)
  //indicates new messages with a new color, and shows number of messages in cache
  val message_ind = new JTextArea("0")
  infopanel.add(message_ind)
  infopanel.add(auto_scroll)
  add (infopanel, BorderLayout.SOUTH)

  // DoubleBuffering for smoother updates
  this.setDoubleBuffered(true)
  message_panel.setDoubleBuffered(true)

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
    message_panel.add (panel)
    panel.setBounds (0, 0, message_panel.getWidth, 1) // document has to fit into width
    panel.doDocumentLayout (panel.getGraphics) //lay out, preferred size is set then
    // if there are thousands of empty panels, all have to be rendered -
    // but this takes time (even for empty panels); therefore minimum size
    panel.setPreferredSize(new java.awt.Dimension(message_panel.getWidth,Math.max(50, panel.getPreferredSize.getHeight.toInt)))
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
        if(panel.getPreferredSize.getWidth.toInt != message_panel.getWidth)
          calculate_preferred_size (panel)
        //place message on view
        val width = panel.getPreferredSize.getWidth.toInt
        val height = panel.getPreferredSize.getHeight.toInt
        panel.setBounds(0, y - height, width, height)
        message_panel.add(panel)
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
    if(message_panel.getComponentCount >= 1){
      message_offset += y
      //remove bottommost panels
      while (message_offset >= message_panel.getComponent(0).getHeight)
      {
        message_offset -= message_panel.getComponent(0).getHeight
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
      if (message_panel.getComponent(message_panel.getComponentCount - 1).getY + y > 0){
        update_view
        update = true
      }
      //simply move panels
      if(!update){
        message_panel.getComponents map (c => {
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
    message_panel.removeAll()
    var n = message_no
    var y:Int = message_panel.getHeight + message_offset
    while (y >= 0 && n >= 0){
      val panel = set_message (n, y)
      panel.setBorder(javax.swing.border.LineBorder.createBlackLineBorder)
      y = y - panel.getHeight
      n = n - 1
    }
    repaint()
  }

  // do not show every new message, wait a certain amount of time
  val message_ind_timer : Timer = new Timer(250, new ActionListener {
      // this method is called to indicate a new message
      override def actionPerformed(e:ActionEvent){
        //fire scroll-event if necessary and wanted
        if(message_no != message_buffer.size
          && auto_scroll.isSelected) {
          vscroll.setValue(message_buffer.size - 1)
        }
        message_ind.setBackground(java.awt.Color.white)
      }
    })

  def add_message (message: Document) = {
    message_buffer += message
    vscroll.setMaximum (Math.max(1, message_buffer.size))
    message_ind.setBackground(java.awt.Color.red)
    message_ind.setText(message_buffer.size.toString)
    if (! message_ind_timer.isRunning()){
      if(auto_scroll.isSelected) vscroll.setValue(message_buffer.size - 1)
      message_ind_timer.setRepeats(false)
      message_ind_timer.start()
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
  
  // TODO: register somewhere
  // here only 'emulation of message stream'
  Plugin.plugin.stateUpdate.add(state => {
    var i = 0
    if(state != null) new Thread{
      override def run() {
        while (i < 500) {
          add_message(state.document)
          i += 1
          try {Thread.sleep(3)}
          catch{case _ =>}
        }
      }
    }.start
  })
}


