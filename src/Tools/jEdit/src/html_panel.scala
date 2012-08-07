/*  Title:      Tools/jEdit/src/html_panel.scala
    Author:     Makarius

HTML panel based on Lobo/Cobra.
*/

package isabelle.jedit


import isabelle._

import java.lang.System
import java.io.StringReader
import java.awt.{Font, BorderLayout, Dimension, GraphicsEnvironment, Toolkit, FontMetrics}
import java.awt.event.MouseEvent

import java.util.logging.{Logger, Level}

import org.w3c.dom.html2.HTMLElement

import org.lobobrowser.html.parser.{DocumentBuilderImpl, InputSourceImpl}
import org.lobobrowser.html.gui.HtmlPanel
import org.lobobrowser.html.domimpl.{HTMLDocumentImpl, HTMLStyleElementImpl, NodeImpl}
import org.lobobrowser.html.test.{SimpleHtmlRendererContext, SimpleUserAgentContext}

import scala.actors.Actor._


object HTML_Panel
{
  sealed abstract class Event { val element: HTMLElement; val mouse: MouseEvent }
  case class Context_Menu(val element: HTMLElement, mouse: MouseEvent) extends Event
  case class Mouse_Click(val element: HTMLElement, mouse: MouseEvent) extends Event
  case class Double_Click(val element: HTMLElement, mouse: MouseEvent) extends Event
  case class Mouse_Over(val element: HTMLElement, mouse: MouseEvent) extends Event
  case class Mouse_Out(val element: HTMLElement, mouse: MouseEvent) extends Event
}


class HTML_Panel(initial_font_family: String, initial_font_size: Int) extends HtmlPanel
{
  /** Lobo setup **/

  /* global logging */

  Logger.getLogger("org.lobobrowser").setLevel(Level.WARNING)


  /* pixel size -- cf. org.lobobrowser.html.style.HtmlValues.getFontSize */

  val screen_resolution =
    if (GraphicsEnvironment.isHeadless()) 72
    else Toolkit.getDefaultToolkit().getScreenResolution()

  def lobo_px(raw_px: Int): Int = raw_px * 96 / screen_resolution
  def raw_px(lobo_px: Int): Int = (lobo_px * screen_resolution + 95) / 96


  /* contexts and event handling */

  protected val handler: PartialFunction[HTML_Panel.Event, Unit] = Map.empty

  private val ucontext = new SimpleUserAgentContext
  private val rcontext = new SimpleHtmlRendererContext(this, ucontext)
  {
    private def handle(event: HTML_Panel.Event): Boolean =
      if (handler.isDefinedAt(event)) { handler(event); false }
      else true

    override def onContextMenu(elem: HTMLElement, event: MouseEvent): Boolean =
      handle(HTML_Panel.Context_Menu(elem, event))
    override def onMouseClick(elem: HTMLElement, event: MouseEvent): Boolean =
      handle(HTML_Panel.Mouse_Click(elem, event))
    override def onDoubleClick(elem: HTMLElement, event: MouseEvent): Boolean =
      handle(HTML_Panel.Double_Click(elem, event))
    override def onMouseOver(elem: HTMLElement, event: MouseEvent)
      { handle(HTML_Panel.Mouse_Over(elem, event)) }
    override def onMouseOut(elem: HTMLElement, event: MouseEvent)
      { handle(HTML_Panel.Mouse_Out(elem, event)) }
  }

  private val builder = new DocumentBuilderImpl(ucontext, rcontext)


  /* document template with style sheets */

  private val template_head =
    """<?xml version="1.0" encoding="utf-8"?>
<!DOCTYPE html PUBLIC "-//W3C//DTD XHTML 1.0 Transitional//EN"
  "http://www.w3.org/TR/xhtml1/DTD/xhtml1-transitional.dtd">
<html xmlns="http://www.w3.org/1999/xhtml">
<head>
<style media="all" type="text/css">
""" +
  File.try_read(Path.split(Isabelle_System.getenv_strict("JEDIT_STYLE_SHEETS")))

  private val template_tail =
"""
</style>
</head>
<body/>
</html>
"""

  private def template(font_family: String, font_size: Int): String =
    template_head +
    "body { font-family: " + font_family + "; font-size: " + raw_px(font_size) + "px; }" +
    template_tail


  /** main actor **/

  /* internal messages */

  private case class Resize(font_family: String, font_size: Int)
  private case class Render_Document(url: String, text: String)
  private case class Render(body: XML.Body)
  private case class Render_Sync(body: XML.Body)
  private case object Refresh

  private val main_actor = actor {

    /* internal state */

    var current_font_metrics: FontMetrics = null
    var current_font_family = ""
    var current_font_size: Int = 0
    var current_margin: Int = 0
    var current_body: XML.Body = Nil

    def resize(font_family: String, font_size: Int)
    {
      val font = new Font(font_family, Font.PLAIN, lobo_px(raw_px(font_size)))
      val (font_metrics, margin) =
        Swing_Thread.now {
          val metrics = getFontMetrics(font)
          (metrics, (getWidth() / (metrics.charWidth(Pretty.spc) max 1) - 4) max 20)
        }
      if (current_font_metrics == null ||
          current_font_family != font_family ||
          current_font_size != font_size ||
          current_margin != margin)
      {
        current_font_metrics = font_metrics
        current_font_family = font_family
        current_font_size = font_size
        current_margin = margin
        refresh()
      }
    }

    def refresh() { render(current_body) }

    def render_document(url: String, text: String)
    {
      val doc = builder.parse(new InputSourceImpl(new StringReader(text), url))
      Swing_Thread.later { setDocument(doc, rcontext) }
    }

    def render(body: XML.Body)
    {
      current_body = body
      val html_body =
        current_body.flatMap(div =>
          Pretty.formatted(List(div), current_margin, Pretty.font_metric(current_font_metrics))
            .map(t =>
              XML.Elem(Markup(HTML.PRE, List((HTML.CLASS, Isabelle_Markup.MESSAGE))),
                HTML.spans(t, true))))
      val doc =
        builder.parse(
          new InputSourceImpl(
            new StringReader(template(current_font_family, current_font_size)), "http://localhost"))
      doc.removeChild(doc.getLastChild())
      doc.appendChild(XML.document_node(doc, XML.elem(HTML.BODY, html_body)))
      Swing_Thread.later { setDocument(doc, rcontext) }
    }


    /* main loop */

    resize(initial_font_family, initial_font_size)

    loop {
      react {
        case Resize(font_family, font_size) => resize(font_family, font_size)
        case Refresh => refresh()
        case Render_Document(url, text) => render_document(url, text)
        case Render(body) => render(body)
        case Render_Sync(body) => render(body); reply(())
        case bad => System.err.println("main_actor: ignoring bad message " + bad)
      }
    }
  }


  /* external methods */

  def resize(font_family: String, font_size: Int) { main_actor ! Resize(font_family, font_size) }
  def refresh() { main_actor ! Refresh }
  def render_document(url: String, text: String) { main_actor ! Render_Document(url, text) }
  def render(body: XML.Body) { main_actor ! Render(body) }
  def render_sync(body: XML.Body) { main_actor !? Render_Sync(body) }
}
