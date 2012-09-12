/*  Title:      Pure/System/html5_panel.scala
    Author:     Makarius

HTML5 panel based on Java FX WebView.
*/

package isabelle

import com.sun.javafx.tk.{FontMetrics, Toolkit}

import javafx.scene.Scene
import javafx.scene.web.{WebView, WebEngine}
import javafx.scene.input.KeyEvent
import javafx.scene.text.{Font, FontSmoothingType}
import javafx.scene.layout.{HBox, VBox, Priority}
import javafx.geometry.{HPos, VPos, Insets}
import javafx.event.EventHandler


// see http://netbeans.org/bugzilla/show_bug.cgi?id=210414
// and http://hg.netbeans.org/jet-main/rev/a88434cec458
private class Web_View_Workaround extends javafx.scene.layout.Pane
{
  VBox.setVgrow(this, Priority.ALWAYS)
  HBox.setHgrow(this, Priority.ALWAYS)

  setMaxWidth(java.lang.Double.MAX_VALUE)
  setMaxHeight(java.lang.Double.MAX_VALUE)

  val web_view = new WebView
  web_view.setMinSize(500, 400)
  web_view.setPrefSize(500, 400)

  getChildren().add(web_view)

  override protected def layoutChildren()
  {
    val managed = getManagedChildren()
    val width = getWidth()
    val height = getHeight()
    val top = getInsets().getTop()
    val right = getInsets().getRight()
    val left = getInsets().getLeft()
    val bottom = getInsets().getBottom()

    for (i <- 0 until managed.size)
      layoutInArea(managed.get(i), left, top,
        width - left - right, height - top - bottom,
        0, Insets.EMPTY, true, true, HPos.CENTER, VPos.CENTER)
  }
}


class HTML5_Panel(main_css: String, init_font_family: String, init_font_size: Int)
  extends javafx.embed.swing.JFXPanel
{
  /* HTML/CSS template */

  def template(font_family: String, font_size: Int): String =
"""<?xml version="1.0" encoding="utf-8"?>
<!DOCTYPE html PUBLIC "-//W3C//DTD XHTML 1.0 Transitional//EN"
  "http://www.w3.org/TR/xhtml1/DTD/xhtml1-transitional.dtd">
<html xmlns="http://www.w3.org/1999/xhtml">
<head>
<style media="all" type="text/css">
""" + main_css +
"body { font-family: " + font_family + "; font-size: " + font_size + "px; }" +
"""
</style>
</head>
<body/>
</html>
"""


  /* main Web view */

  private val future =
    JFX_Thread.future {
      val pane = new Web_View_Workaround

      val web_view = pane.web_view
      web_view.setFontSmoothingType(FontSmoothingType.GRAY)
      web_view.setOnKeyTyped(new EventHandler[KeyEvent] {
        def handle(e: KeyEvent) {
          if (e.isControlDown && e.getCharacter == "0")
            web_view.setFontScale(1.0)
          if (e.isControlDown && e.getCharacter == "+")
            web_view.setFontScale(web_view.getFontScale * 1.1)
          else if (e.isControlDown && e.getCharacter == "-")
            web_view.setFontScale(web_view.getFontScale / 1.1)
        }
      })

      setScene(new Scene(pane))

      web_view.getEngine.loadContent(template(init_font_family, init_font_size))
      pane
    }

  def web_view: WebView = future.join.web_view
  def web_engine: WebEngine = web_view.getEngine


  /* internal state -- owned by JFX thread */

  private var current_font_metrics: FontMetrics = null
  private var current_font_family = ""
  private var current_font_size: Int = 0
  private var current_margin: Int = 0
  private var current_body: XML.Body = Nil

  // FIXME move to pretty.scala (!?)
  private def pretty_metric(metrics: FontMetrics): String => Double =
  {
    if (metrics == null) ((s: String) => s.length.toDouble)
    else {
      val unit = metrics.computeStringWidth(Pretty.space).toDouble
      ((s: String) => if (s == "\n") 1.0 else metrics.computeStringWidth(s) / unit)
    }
  }

  def resize(font_family: String, font_size: Int): Unit = JFX_Thread.later {
    val font = new Font(font_family, font_size)
    val font_metrics = Toolkit.getToolkit().getFontLoader().getFontMetrics(font)
    val margin =  // FIXME Swing thread!?
      (getWidth() / (font_metrics.computeStringWidth(Pretty.space) max 1.0f)).toInt max 20

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

  def refresh(): Unit = JFX_Thread.later { render(current_body) }

  def render(body: XML.Body): Unit = JFX_Thread.later {
    current_body = body
    val html_body =
      current_body.flatMap(div =>
        Pretty.formatted(List(div), current_margin, pretty_metric(current_font_metrics))
          .map(t =>
            XML.Elem(Markup(HTML.PRE, List((HTML.CLASS, Isabelle_Markup.MESSAGE))),
              HTML.spans(t, false))))  // FIXME user data (!??!)

    // FIXME  web_engine.loadContent(template(current_font_family, current_font_size))

    val document = web_engine.getDocument
    val html_root = document.getLastChild
    html_root.removeChild(html_root.getLastChild)
    html_root.appendChild(XML.document_node(document, XML.elem(HTML.BODY, html_body)))
  }
}
