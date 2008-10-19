package isabelle.jedit

import java.io.{ ByteArrayInputStream, FileInputStream, InputStream }

import java.awt.GridLayout
import javax.swing.{ JPanel, JTextArea, JScrollPane }

import isabelle.IsabelleSystem.getenv

import org.xml.sax.InputSource;

import org.w3c.dom.Document

import org.xhtmlrenderer.simple.XHTMLPanel
import org.xhtmlrenderer.context.AWTFontResolver
import org.xhtmlrenderer.swing.NaiveUserAgent
import org.xhtmlrenderer.resource.CSSResource

import org.gjt.sp.jedit.View

object StateViewDockable {
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

class UserAgent extends NaiveUserAgent {
  override def getCSSResource(uri : String) : CSSResource = {
    if (uri == StateViewDockable.baseURL + "style")
      new CSSResource(
        new ByteArrayInputStream(StateViewDockable.stylesheet.getBytes()))
    else {
      val stream = resolveAndOpenStream(uri)
      val resource = new CSSResource(stream)
      if (stream == null)
        resource.getResourceInputSource().setByteStream(
          new ByteArrayInputStream(new Array[Byte](0)))
      resource
    }
  }
}

class StateViewDockable(view : View, position : String) extends JPanel {
  {
    val panel = new XHTMLPanel(new UserAgent())
    setLayout(new GridLayout(1, 1))
    add(new JScrollPane(panel))
    
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
        panel.setDocument(state.document, StateViewDockable.baseURL)
    })
  }
}
