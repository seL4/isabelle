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

object ScrollerDockable {
  val baseURL = "file://localhost" + getenv("ISABELLE_HOME") + "/lib/html/"
  val userStylesheet = 
    "file://localhost" + getenv("ISABELLE_HOME_USER") + "/etc/user.css";
  val stylesheet = """

@import "isabelle.css";

@import '""" + userStylesheet + """';

messages, message {
  display: block;
  white-space: pre-wrap;
  font-family: Isabelle;
}
"""
}


class ScrollerDockable(view : View, position : String) extends JPanel with AdjustmentListener with ComponentListener {
  //holding the unrendered messages
  val message_buffer = new ArrayBuffer[Document]()
  //rendered messages
  var message_cache = Map[Int, XHTMLPanel]()
  // defining the current view
  val scrollunit = 10 
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

    panel.setDocument(message, ScrollerDockable.baseURL)
    panel
  }
  
  //calculates preferred size of panel
  def calculate_preferred_size(panel: XHTMLPanel){
    message_view.add (panel)
    panel.setBounds (0, 0, message_view.getWidth, 1) // document has to fit into width
    panel.doLayout (panel.getGraphics) //lay out, preferred size is set then
  }
  
  //add panel to the cache
  def add_to_cache (message_no: Int, panel: XHTMLPanel) = {
    message_cache = message_cache.update (message_no, panel)
    calculate_preferred_size(panel)
    System.err.println("Added " + message_no + " with preferred Size " + panel.getPreferredSize + " to cache")
  }
  
  //render and load a message into cache, place its bottom at y-coordinate;
  def set_message (message_no: Int, y: Int) = {
    //get or add panel from/to cache
    if(!message_cache.isDefinedAt(message_no)){
      add_to_cache (message_no, render (message_buffer(message_no)))
    }
    val panel = message_cache.get(message_no).get
    val width = panel.getPreferredSize.getWidth.toInt
    val height = panel.getPreferredSize.getHeight.toInt
    panel.setBounds(0, y - height, width, height)
    message_view.add(panel)
    panel
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
  }

  override def adjustmentValueChanged (e : AdjustmentEvent) = {
    //event-handling has to be so general (without UNIT_INCR,...)
    // because all events could be sent as TRACK e.g. on my mac
    message_no = e.getValue
    update_view
  }

  // handle Component-Events
  override def componentShown(e: ComponentEvent){}
  override def componentHidden(e: ComponentEvent){}
  override def componentMoved(e: ComponentEvent){}
  override def componentResized(e: ComponentEvent){
    // remove all hidden messages from cache
    // TODO: move to unlayouted cache
    message_cache = message_cache filter ( pair => pair match {case (no, _) =>
      no <= message_no && no >= message_no - message_view.getComponents.length})
    //calculate preferred size for each panel
    message_cache foreach (pair => pair match { case (_, pa) =>
      calculate_preferred_size (pa)
    })
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


