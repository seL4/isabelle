/*  Title:      Tools/jEdit/src/jedit/html_panel.scala
    Author:     Makarius

HTML panel based on Lobo/Cobra.
*/

package isabelle.jedit


import isabelle._

import java.io.StringReader
import java.awt.{BorderLayout, Dimension, GraphicsEnvironment, Toolkit, FontMetrics}
import java.awt.event.MouseEvent

import javax.swing.{JButton, JPanel, JScrollPane}
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


class HTML_Panel(
  system: Isabelle_System,
  initial_font_size: Int,
  handler: PartialFunction[HTML_Panel.Event, Unit]) extends HtmlPanel
{
  // global logging
  Logger.getLogger("org.lobobrowser").setLevel(Level.WARNING)


  /* Lobo setup */

  // pixel size -- cf. org.lobobrowser.html.style.HtmlValues.getFontSize
  val screen_resolution =
    if (GraphicsEnvironment.isHeadless()) 72
    else Toolkit.getDefaultToolkit().getScreenResolution()

  def lobo_px(raw_px: Int): Int = raw_px * 96 / screen_resolution
  def raw_px(lobo_px: Int): Int = (lobo_px * screen_resolution + 95) / 96


  private val ucontext = new SimpleUserAgentContext
  private val rcontext = new SimpleHtmlRendererContext(this, ucontext)
  {
    private def handle(event: HTML_Panel.Event): Boolean =
      if (handler != null && handler.isDefinedAt(event)) { handler(event); true }
      else false

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


  /* physical document */

  private def template(font_size: Int): String =
  {
    """<?xml version="1.0" encoding="utf-8"?>
<!DOCTYPE html PUBLIC "-//W3C//DTD XHTML 1.0 Transitional//EN"
  "http://www.w3.org/TR/xhtml1/DTD/xhtml1-transitional.dtd">
<html xmlns="http://www.w3.org/1999/xhtml">
<head>
<style media="all" type="text/css">
""" +
  system.try_read("$ISABELLE_HOME/lib/html/isabelle.css") + "\n" +
  system.try_read("$ISABELLE_HOME_USER/etc/isabelle.css") + "\n" +
  "body { font-family: " + system.font_family + "; font-size: " + raw_px(font_size) + "px }" +
"""
</style>
</head>
<body/>
</html>
"""
  }

  private class Doc
  {
    var current_font_size: Int = 0
    var current_font_metrics: FontMetrics = null
    var current_margin: Int = 0
    var current_body: List[XML.Tree] = Nil
    var current_DOM: org.w3c.dom.Document = null

    def resize(font_size: Int)
    {
      if (font_size != current_font_size || current_font_metrics == null) {
        Swing_Thread.now {
          current_font_size = font_size
          current_font_metrics =
            getFontMetrics(system.get_font(lobo_px(raw_px(font_size))))
          current_margin =
            (getWidth() / (current_font_metrics.charWidth(Symbol.spc) max 1) - 4) max 20
        }
        current_DOM =
          builder.parse(
            new InputSourceImpl(new StringReader(template(font_size)), "http://localhost"))
        render(current_body)
      }
    }

    def render(body: List[XML.Tree])
    {
      current_body = body
      val html_body =
        current_body.flatMap(div =>
          Pretty.formatted(List(div), current_margin,
              Pretty.font_metric(current_font_metrics))
            .map(t => XML.elem(HTML.PRE, HTML.spans(t))))

      val node = XML.document_node(current_DOM, XML.elem(HTML.BODY, html_body))
      current_DOM.removeChild(current_DOM.getLastChild())
      current_DOM.appendChild(node)
      Swing_Thread.now { setDocument(current_DOM, rcontext) }
    }

    resize(initial_font_size)
  }


  /* main actor and method wrappers */

  private case class Resize(font_size: Int)
  private case class Render(body: List[XML.Tree])

  private val main_actor = actor {
    var doc = new Doc
    loop {
      react {
        case Resize(font_size) => doc.resize(font_size)
        case Render(body) => doc.render(body)
        case bad => System.err.println("main_actor: ignoring bad message " + bad)
      }
    }
  }

  def resize(font_size: Int) { main_actor ! Resize(font_size) }
  def render(body: List[XML.Tree]) { main_actor ! Render(body) }
}
