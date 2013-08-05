/*  Title:      Tools/jEdit/src/jedit_lib.scala
    Author:     Makarius

Misc library functions for jEdit.
*/

package isabelle.jedit


import isabelle._

import java.awt.{Component, Container, Window, GraphicsEnvironment, Point, Rectangle}
import javax.swing.{Icon, ImageIcon}

import scala.annotation.tailrec

import org.gjt.sp.jedit.{jEdit, Buffer, View, GUIUtilities}
import org.gjt.sp.jedit.buffer.JEditBuffer
import org.gjt.sp.jedit.textarea.{JEditTextArea, TextArea, TextAreaPainter}


object JEdit_Lib
{
  /* bounds within multi-screen environment */

  def screen_bounds(screen_point: Point): Rectangle =
  {
    val ge = GraphicsEnvironment.getLocalGraphicsEnvironment
    (for {
      device <- ge.getScreenDevices.iterator
      config <- device.getConfigurations.iterator
      bounds = config.getBounds
    } yield bounds).find(_.contains(screen_point)) getOrElse ge.getMaximumWindowBounds
  }


  /* GUI components */

  def get_parent(component: Component): Option[Container] =
    component.getParent match {
      case null => None
      case parent => Some(parent)
    }

  def ancestors(component: Component): Iterator[Container] = new Iterator[Container] {
    private var next_elem = get_parent(component)
    def hasNext(): Boolean = next_elem.isDefined
    def next(): Container =
      next_elem match {
        case Some(parent) =>
          next_elem = get_parent(parent)
          parent
        case None => Iterator.empty.next()
      }
  }

  def parent_window(component: Component): Option[Window] =
    ancestors(component).collectFirst({ case x: Window => x })


  /* basic tooltips, with multi-line support */

  def wrap_tooltip(text: String): String =
    if (text == "") null
    else "<html><pre>" + HTML.encode(text) + "</pre></html>"


  /* buffers */

  def swing_buffer_lock[A](buffer: JEditBuffer)(body: => A): A =
    Swing_Thread.now { buffer_lock(buffer) { body } }

  def buffer_text(buffer: JEditBuffer): String =
    buffer_lock(buffer) { buffer.getText(0, buffer.getLength) }

  def buffer_name(buffer: Buffer): String = buffer.getSymlinkPath


  /* main jEdit components */

  def jedit_buffers(): Iterator[Buffer] = jEdit.getBuffers().iterator

  def jedit_buffer(name: String): Option[Buffer] =
    jedit_buffers().find(buffer => buffer_name(buffer) == name)

  def jedit_views(): Iterator[View] = jEdit.getViews().iterator

  def jedit_text_areas(view: View): Iterator[JEditTextArea] =
    view.getEditPanes().iterator.map(_.getTextArea)

  def jedit_text_areas(): Iterator[JEditTextArea] =
    jedit_views().flatMap(jedit_text_areas(_))

  def jedit_text_areas(buffer: JEditBuffer): Iterator[JEditTextArea] =
    jedit_text_areas().filter(_.getBuffer == buffer)

  def buffer_lock[A](buffer: JEditBuffer)(body: => A): A =
  {
    try { buffer.readLock(); body }
    finally { buffer.readUnlock() }
  }

  def buffer_edit[A](buffer: JEditBuffer)(body: => A): A =
  {
    try { buffer.beginCompoundEdit(); body }
    finally { buffer.endCompoundEdit() }
  }


  /* get text */

  def try_get_text(buffer: JEditBuffer, range: Text.Range): Option[String] =
    try { Some(buffer.getText(range.start, range.length)) }
    catch { case _: ArrayIndexOutOfBoundsException => None }


  /* buffer range */

  def buffer_range(buffer: JEditBuffer): Text.Range =
    Text.Range(0, (buffer.getLength - 1) max 0)


  /* point range */

  def point_range(buffer: JEditBuffer, offset: Text.Offset): Text.Range =
    buffer_lock(buffer) {
      def text(i: Text.Offset): Char = buffer.getText(i, 1).charAt(0)
      try {
        val c = text(offset)
        if (Character.isHighSurrogate(c) && Character.isLowSurrogate(text(offset + 1)))
          Text.Range(offset, offset + 2)
        else if (Character.isLowSurrogate(c) && Character.isHighSurrogate(text(offset - 1)))
          Text.Range(offset - 1, offset + 1)
        else Text.Range(offset, offset + 1)
      }
      catch { case _: ArrayIndexOutOfBoundsException => Text.Range(offset, offset + 1) }
    }


  /* visible text range */

  def visible_range(text_area: TextArea): Option[Text.Range] =
  {
    val buffer = text_area.getBuffer
    val n = text_area.getVisibleLines
    if (n > 0) {
      val start = text_area.getScreenLineStartOffset(0)
      val raw_end = text_area.getScreenLineEndOffset(n - 1)
      val end = if (raw_end >= 0) raw_end min buffer.getLength else buffer.getLength
      Some(Text.Range(start, end))
    }
    else None
  }

  def invalidate_range(text_area: TextArea, range: Text.Range)
  {
    val buffer = text_area.getBuffer
    text_area.invalidateLineRange(
      buffer.getLineOfOffset(range.start),
      buffer.getLineOfOffset(range.stop))
  }


  /* graphics range */

  case class Gfx_Range(val x: Int, val y: Int, val length: Int)

  // NB: jEdit always normalizes \r\n and \r to \n
  // NB: last line lacks \n
  def gfx_range(text_area: TextArea, range: Text.Range): Option[Gfx_Range] =
  {
    val metric = pretty_metric(text_area.getPainter)
    val char_width = (metric.unit * metric.average).round.toInt

    val buffer = text_area.getBuffer

    val end = buffer.getLength
    val stop = range.stop

    val (p, q, r) =
      try {
        val p = text_area.offsetToXY(range.start)
        val (q, r) =
          if (stop >= end) (text_area.offsetToXY(end), char_width * (stop - end))
          else if (stop > 0 && buffer.getText(stop - 1, 1) == "\n")
            (text_area.offsetToXY(stop - 1), char_width)
          else (text_area.offsetToXY(stop), 0)
        (p, q, r)
      }
      catch { case _: ArrayIndexOutOfBoundsException => (null, null, 0) }

    if (p != null && q != null && p.x < q.x + r && p.y == q.y)
      Some(Gfx_Range(p.x, p.y, q.x + r - p.x))
    else None
  }


  /* pixel range */

  def pixel_range(text_area: TextArea, x: Int, y: Int): Option[Text.Range] =
  {
    val range = point_range(text_area.getBuffer, text_area.xyToOffset(x, y, false))
    gfx_range(text_area, range) match {
      case Some(g) if (g.x <= x && x < g.x + g.length) => Some(range)
      case _ => None
    }
  }


  /* pretty text metric */

  abstract class Pretty_Metric extends Pretty.Metric
  {
    def average: Double
  }

  def pretty_metric(painter: TextAreaPainter): Pretty_Metric =
    new Pretty_Metric {
      def string_width(s: String): Double =
        painter.getFont.getStringBounds(s, painter.getFontRenderContext).getWidth

      val unit = string_width(Pretty.space)
      val average = string_width("mix") / (3 * unit)
      def apply(s: String): Double = if (s == "\n") 1.0 else string_width(s) / unit
    }


  /* icons */

  def load_icon(name: String): Icon =
  {
    val name1 =
      if (name.startsWith("idea-icons/")) {
        val file =
          Isabelle_System.platform_file_url(Path.explode("$JEDIT_HOME/dist/jars/idea-icons.jar"))
        "jar:" + file + "!/" + name
      }
      else name
    val icon = GUIUtilities.loadIcon(name1)
    if (icon.getIconWidth < 0 || icon.getIconHeight < 0) error("Bad icon: " + name)
    else icon
  }

  def load_image_icon(name: String): ImageIcon =
    load_icon(name) match {
      case icon: ImageIcon => icon
      case _ => error("Bad image icon: " + name)
    }
}

