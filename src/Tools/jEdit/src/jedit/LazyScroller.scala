/*
 * LazyScroller.scala
 *
 *
 */

package isabelle.jedit

import java.io.{ ByteArrayInputStream, FileInputStream, InputStream }

import scala.collection.mutable.ArrayBuffer
import scala.collection.jcl.ArrayList

import java.awt.{ BorderLayout, GridLayout, Adjustable, Rectangle, Scrollbar }
import java.awt.image.BufferedImage
import java.awt.event.{ AdjustmentListener, AdjustmentEvent }
import javax.swing.{ JScrollBar, JPanel, JScrollPane, ScrollPaneConstants }

import isabelle.IsabelleSystem.getenv

import org.xml.sax.InputSource;

import org.w3c.dom.Document

import org.xhtmlrenderer.simple.XHTMLPanel
import org.xhtmlrenderer.context.AWTFontResolver
import org.xhtmlrenderer.swing.NaiveUserAgent
import org.xhtmlrenderer.resource.CSSResource

import org.gjt.sp.jedit.View

object LazyScroller {
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


abstract class LazyScroller[T] extends JPanel with AdjustmentListener{
  //holding the unrendered messages
  val message_buffer = new ArrayBuffer[T]()
  // defining the current view
  val scrollunit = 10 //TODO: not used
  var message_offset = 0 //TODO: not used; how many pixels of the topmost message are hidden
  var message_no = 0  //index of the topmost message
  var message_view = new JPanel
  message_view.setLayout(new GridLayout(1,1))
  // setting up view
  setLayout(new BorderLayout())
  val vscroll = new JScrollBar(Adjustable.VERTICAL, 0, 1, 0, 1)
  vscroll.addAdjustmentListener(this)
  add (vscroll, BorderLayout.EAST)
  add (message_view, BorderLayout.CENTER)


  // subclasses should implement this
  def render (message : T) : JPanel

  //TODO: - add more than one message
  //      - render only when necessary
  def update_view = {
    message_view.removeAll()
    val rendered_message = render (message_buffer(message_no))
    val resizable = new JScrollPane(rendered_message, ScrollPaneConstants.VERTICAL_SCROLLBAR_NEVER, ScrollPaneConstants.HORIZONTAL_SCROLLBAR_NEVER)
    message_view.add (resizable)
  }
  
  def update_scrollbar = {
    vscroll.setValue (message_no)
    vscroll.setMaximum (Math.max(1, message_buffer.length))
  }

  def add_message (message : T) = {
    message_buffer += message
  }

  override def adjustmentValueChanged (e : AdjustmentEvent) = {
    //TODO: find out if all Swing-Implementations handle scrolling as *only* TRACK
    e.getAdjustmentType match {
      //Scroll shown messages up
      case AdjustmentEvent.UNIT_INCREMENT =>

      //Scroll shown messages down
      case AdjustmentEvent.UNIT_DECREMENT =>

      // Jump to next message
      case AdjustmentEvent.BLOCK_INCREMENT =>

      //Jump to previous message
      case AdjustmentEvent.BLOCK_DECREMENT =>

      //Jump to message
      case AdjustmentEvent.TRACK =>
        message_no = e.getValue
        update_view
      case _ =>
    }
  }
  }


class XMLScroller(view : View, position : String) extends LazyScroller[Document] {
  
    Plugin.plugin.stateUpdate.add(state => {
        var i = 0
        if(state != null) while (i < 1000) {
          add_message(state.document)
          i += 1
        }
        //TODO: only a hack:
        update_scrollbar
    })

    def render (message: Document): JPanel = {
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

      panel.setDocument(message, LazyScroller.baseURL)
      panel
    }
 }

