/*  Title:      Tools/jEdit/src/html_panel.scala
    Author:     Makarius

HTML panel based on Lobo/Cobra.
*/

package isabelle.jedit


import isabelle._

import java.io.StringReader

import java.util.logging.{Logger, Level}

import org.lobobrowser.html.parser.{DocumentBuilderImpl, InputSourceImpl}
import org.lobobrowser.html.gui.HtmlPanel
import org.lobobrowser.html.test.{SimpleHtmlRendererContext, SimpleUserAgentContext}


class HTML_Panel extends HtmlPanel
{
  Swing_Thread.require()

  Logger.getLogger("org.lobobrowser").setLevel(Level.WARNING)

  private val ucontext = new SimpleUserAgentContext
  private val rcontext = new SimpleHtmlRendererContext(this, ucontext)
  private val builder = new DocumentBuilderImpl(ucontext, rcontext)

  def render_document(url: String, html_text: String)
  {
    val doc = builder.parse(new InputSourceImpl(new StringReader(html_text), url))
    Swing_Thread.later { setDocument(doc, rcontext) }
  }
}
