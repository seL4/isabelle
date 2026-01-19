/*  Title:      Tools/jEdit/src/document_view.scala
    Author:     Fabian Immler, TU Munich
    Author:     Makarius

Document view connected to jEdit text area.
*/

package isabelle.jedit


import isabelle._

import java.awt.Graphics2D
import java.awt.event.KeyEvent
import java.awt.geom.AffineTransform
import javax.swing.event.{CaretListener, CaretEvent}

import org.gjt.sp.jedit.jEdit
import org.gjt.sp.jedit.options.GutterOptionPane
import org.gjt.sp.jedit.textarea.{JEditTextArea, TextArea, TextAreaExtension, TextAreaPainter,
  Gutter}


object Document_View {
  /* document view of text area */

  private val key = new Object

  def get(text_area: TextArea): Option[Document_View] = {
    GUI_Thread.require {}
    text_area.getClientProperty(key) match {
      case doc_view: Document_View => Some(doc_view)
      case _ => None
    }
  }

  def exit(text_area: JEditTextArea): Unit = {
    GUI_Thread.require {}
    get(text_area) match {
      case None =>
      case Some(doc_view) =>
        doc_view.deactivate()
        text_area.putClientProperty(key, null)
    }
  }

  def init(model: Buffer_Model, text_area: JEditTextArea): Document_View = {
    exit(text_area)
    val doc_view = new Document_View(model, text_area)
    text_area.putClientProperty(key, doc_view)
    doc_view.activate()
    doc_view
  }

  def rendering(doc_view: Document_View): JEdit_Rendering = {
    val model = doc_view.model
    val snapshot = Document_Model.snapshot(model)
    val options = PIDE.options
    new JEdit_Rendering(snapshot, model, options)
  }

  def get_rendering(text_area: TextArea): Option[JEdit_Rendering] = get(text_area).map(rendering)
}

class Document_View(val model: Buffer_Model, val text_area: JEditTextArea) {
  doc_view =>

  private val session = model.session

  val rich_text_area: Rich_Text_Area =
    new Rich_Text_Area(text_area.getView, text_area,
      () => Document_View.rendering(doc_view), () => (), () => None,
      () => delay_caret_update.invoke(), caret_visible = true, enable_hovering = false)


  /* perspective */

  def perspective(snapshot: Document.Snapshot): Text.Perspective = {
    GUI_Thread.require {}

    val active_command = {
      val view = text_area.getView
      if (view != null && view.getTextArea == text_area) {
        PIDE.editor.current_command(view, snapshot) match {
          case Some(command) =>
            snapshot.node.command_start(command) match {
              case Some(start) => List(snapshot.convert(command.core_range + start))
              case None => Nil
            }
          case None => Nil
        }
      }
      else Nil
    }

    val buffer_range = JEdit_Lib.buffer_range(model.buffer)
    val visible_lines =
      (for {
        i <- (0 until text_area.getVisibleLines).iterator
        start = text_area.getScreenLineStartOffset(i)
        stop = text_area.getScreenLineEndOffset(i)
        if start >= 0 && stop >= 0
        range <- buffer_range.try_restrict(Text.Range(start, stop))
        if !range.is_singularity
      }
      yield range).toList

    Text.Perspective(active_command ::: visible_lines)
  }

  private def update_view = new TextAreaExtension {
    override def paintScreenLineRange(
      gfx: Graphics2D,
      first_line: Int,
      last_line: Int,
      physical_lines: Array[Int],
      start: Array[Int],
      end: Array[Int],
      y: Int,
      line_height: Int
    ): Unit = {
      // no robust_body
      PIDE.editor.invoke_generated()
    }
  }


  /* gutter */

  private val gutter_painter = new TextAreaExtension {
    override def paintScreenLineRange(
      gfx: Graphics2D,
      first_line: Int,
      last_line: Int,
      physical_lines: Array[Int],
      start: Array[Int],
      end: Array[Int],
      y: Int,
      line_height: Int
    ): Unit = {
      rich_text_area.robust_body(()) {
        GUI_Thread.assert {}

        val gutter = text_area.getGutter
        val gutter_width = gutter.getWidth
        val gutter_insets = gutter.getBorder.getBorderInsets(gutter)

        val skip_left = gutter_insets.left + Gutter.FOLD_MARKER_SIZE
        val skip_right = gutter_insets.right
        val icon_width = gutter_width - skip_left - skip_right
        val icon_height = line_height

        def scale(a: Int, b: Int): Double = 0.95 * a.toDouble / b.toDouble

        val gutter_icons =
          !gutter.isExpanded &&
            gutter.isSelectionAreaEnabled && icon_width >= 12 && icon_height >= 12

        val buffer = model.buffer
        JEdit_Lib.buffer_lock(buffer) {
          val rendering = Document_View.rendering(doc_view)

          for (i <- physical_lines.indices) {
            if (physical_lines(i) != -1) {
              val line_range = Text.Range(start(i), end(i))

              rendering.gutter_content(line_range) match {
                case Some((icon, color)) =>
                  // icons within selection area
                  if (gutter_icons && icon.getIconWidth > 0 && icon.getIconHeight > 0) {
                    val w0 = icon.getIconWidth
                    val h0 = icon.getIconHeight
                    val s = Math.min(scale(icon_width, w0), scale(icon_height, h0))

                    val w = (s * w0).ceil
                    val h = (s * h0).ceil
                    val x0 = skip_left + (((icon_width - w) / 2) max 0)
                    val y0 = y + i * line_height + (((icon_height - h) / 2) max 0)

                    val tr0 = gfx.getTransform
                    val tr = new AffineTransform(tr0); tr.translate(x0, y0); tr.scale(s, s)
                    gfx.setTransform(tr)
                    icon.paintIcon(gutter, gfx, 0, 0)
                    gfx.setTransform(tr0)
                  }
                  // background only
                  else {
                    val y0 = y + i * line_height
                    gfx.setColor(color)
                    gfx.fillRect(0, y0, gutter_width, line_height)
                  }
                case None =>
              }
            }
          }
        }
      }
    }
  }


  /* key listener */

  private val key_listener =
    JEdit_Lib.key_listener(
      key_pressed = { (evt: KeyEvent) =>
        if (evt.getKeyCode == KeyEvent.VK_ESCAPE && Isabelle.dismissed_popups(text_area.getView)) {
          evt.consume()
        }
      }
    )


  /* caret handling */

  private val delay_caret_update =
    Delay.last(PIDE.session.input_delay, gui = true) {
      session.caret_focus.post(Session.Caret_Focus)
      JEdit_Lib.invalidate_screen(text_area)
    }

  private val caret_listener = new CaretListener {
    override def caretUpdate(e: CaretEvent): Unit = delay_caret_update.invoke()
  }


  /* text status overview left of scrollbar */

  private val text_overview: Option[Text_Overview] =
    if (PIDE.options.bool("jedit_text_overview")) Some(new Text_Overview(doc_view)) else None


  /* main */

  private val main =
    Session.Consumer[Any](getClass.getName) {
      case _: Session.Raw_Edits =>
        text_overview.foreach(_.invoke())

      case changed: Session.Commands_Changed =>
        val buffer = model.buffer
        GUI_Thread.later {
          JEdit_Lib.buffer_lock(buffer) {
            if (model.buffer == text_area.getBuffer) {
              val snapshot = Document_Model.snapshot(model)

              if (changed.assignment ||
                  (changed.nodes.contains(model.node_name) &&
                   changed.commands.exists(snapshot.node.commands.contains)))
                text_overview.foreach(_.invoke())

              JEdit_Lib.invalidate_screen(text_area)
            }
          }
        }
    }


  /* activation */

  private def activate(): Unit = {
    val painter = text_area.getPainter

    painter.addExtension(TextAreaPainter.LOWEST_LAYER, update_view)
    rich_text_area.activate()
    text_area.getGutter.addExtension(gutter_painter)
    text_area.addKeyListener(key_listener)
    text_area.addCaretListener(caret_listener)
    text_overview.foreach(text_area.addLeftOfScrollBar(_))
    text_area.revalidate()
    text_area.repaint()
    Isabelle.structure_matchers(JEdit_Lib.buffer_mode(text_area.getBuffer)).
      foreach(text_area.addStructureMatcher)
    session.raw_edits += main
    session.commands_changed += main
  }

  private def deactivate(): Unit = {
    val painter = text_area.getPainter

    session.raw_edits -= main
    session.commands_changed -= main
    Isabelle.structure_matchers(JEdit_Lib.buffer_mode(text_area.getBuffer)).
      foreach(text_area.removeStructureMatcher)
    text_overview.foreach(_.revoke())
    text_overview.foreach(text_area.removeLeftOfScrollBar(_))
    text_area.removeCaretListener(caret_listener)
    delay_caret_update.revoke()
    text_area.removeKeyListener(key_listener)
    text_area.getGutter.removeExtension(gutter_painter)
    rich_text_area.deactivate()
    painter.removeExtension(update_view)
  }
}
