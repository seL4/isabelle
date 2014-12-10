/*  Title:      Tools/jEdit/src/document_view.scala
    Author:     Fabian Immler, TU Munich
    Author:     Makarius

Document view connected to jEdit text area.
*/

package isabelle.jedit


import isabelle._

import java.awt.Graphics2D
import java.awt.event.KeyEvent
import javax.swing.event.{CaretListener, CaretEvent}

import org.gjt.sp.jedit.jEdit
import org.gjt.sp.jedit.options.GutterOptionPane
import org.gjt.sp.jedit.textarea.{JEditTextArea, TextArea, TextAreaExtension, TextAreaPainter}


object Document_View
{
  /* document view of text area */

  private val key = new Object

  def apply(text_area: TextArea): Option[Document_View] =
  {
    GUI_Thread.require {}
    text_area.getClientProperty(key) match {
      case doc_view: Document_View => Some(doc_view)
      case _ => None
    }
  }

  def exit(text_area: JEditTextArea)
  {
    GUI_Thread.require {}
    apply(text_area) match {
      case None =>
      case Some(doc_view) =>
        doc_view.deactivate()
        text_area.putClientProperty(key, null)
    }
  }

  def init(model: Document_Model, text_area: JEditTextArea): Document_View =
  {
    exit(text_area)
    val doc_view = new Document_View(model, text_area)
    text_area.putClientProperty(key, doc_view)
    doc_view.activate()
    doc_view
  }
}


class Document_View(val model: Document_Model, val text_area: JEditTextArea)
{
  private val session = model.session

  def get_rendering(): Rendering = Rendering(model.snapshot(), PIDE.options.value)

  val rich_text_area =
    new Rich_Text_Area(text_area.getView, text_area, get_rendering _, () => (),
      () => None, caret_visible = true, enable_hovering = false)


  /* perspective */

  def perspective(snapshot: Document.Snapshot): Text.Perspective =
  {
    GUI_Thread.require {}

    val active_command =
    {
      val view = text_area.getView
      if (view != null && view.getTextArea == text_area) {
        PIDE.editor.current_command(view, snapshot) match {
          case Some(command) =>
            snapshot.node.command_start(command) match {
              case Some(start) => List(snapshot.convert(command.proper_range + start))
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

  private def update_view = new TextAreaExtension
  {
    override def paintScreenLineRange(gfx: Graphics2D,
      first_line: Int, last_line: Int, physical_lines: Array[Int],
      start: Array[Int], end: Array[Int], y: Int, line_height: Int)
    {
      // no robust_body
      PIDE.editor.invoke()
    }
  }


  /* gutter */

  private val gutter_painter = new TextAreaExtension
  {
    override def paintScreenLineRange(gfx: Graphics2D,
      first_line: Int, last_line: Int, physical_lines: Array[Int],
      start: Array[Int], end: Array[Int], y: Int, line_height: Int)
    {
      rich_text_area.robust_body(()) {
        GUI_Thread.assert {}

        val gutter = text_area.getGutter
        val sel_width = GutterOptionPane.getSelectionAreaWidth
        val border_width = jEdit.getIntegerProperty("view.gutter.borderWidth", 3)
        val FOLD_MARKER_SIZE = 12

        val buffer = model.buffer
        JEdit_Lib.buffer_lock(buffer) {
          val rendering = get_rendering()

          for (i <- 0 until physical_lines.length) {
            if (physical_lines(i) != -1) {
              val line_range = Text.Range(start(i), end(i))

              rendering.gutter_content(line_range) match {
                case Some((icon, color)) =>
                  // icons within selection area
                  if (!gutter.isExpanded &&
                      gutter.isSelectionAreaEnabled && sel_width >= 12 && line_height >= 12)
                  {
                    val x0 =
                      (FOLD_MARKER_SIZE + sel_width - border_width - icon.getIconWidth) max 10
                    val y0 =
                      y + i * line_height + (((line_height - icon.getIconHeight) / 2) max 0)
                    icon.paintIcon(gutter, gfx, x0, y0)
                  }
                  // background
                  else {
                    val y0 = y + i * line_height
                    gfx.setColor(color)
                    gfx.fillRect(0, y0, gutter.getWidth, line_height)
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
      key_pressed = (evt: KeyEvent) =>
        {
          if (evt.getKeyCode == KeyEvent.VK_ESCAPE && PIDE.dismissed_popups(text_area.getView))
            evt.consume
        }
    )


  /* caret handling */

  private val delay_caret_update =
    GUI_Thread.delay_last(PIDE.options.seconds("editor_input_delay")) {
      session.caret_focus.post(Session.Caret_Focus)
    }

  private val caret_listener = new CaretListener {
    override def caretUpdate(e: CaretEvent) { delay_caret_update.invoke() }
  }


  /* text status overview left of scrollbar */

  private object overview extends Text_Overview(this)
  {
    val delay_repaint =
      GUI_Thread.delay_first(PIDE.options.seconds("editor_update_delay")) { repaint() }
  }


  /* main */

  private val main =
    Session.Consumer[Any](getClass.getName) {
      case _: Session.Raw_Edits =>
        overview.delay_repaint.postpone(PIDE.options.seconds("editor_input_delay"))

      case changed: Session.Commands_Changed =>
        val buffer = model.buffer
        GUI_Thread.later {
          JEdit_Lib.buffer_lock(buffer) {
            if (model.buffer == text_area.getBuffer) {
              val snapshot = model.snapshot()

              val load_changed =
                snapshot.load_commands.exists(changed.commands.contains)

              if (changed.assignment || load_changed ||
                  (changed.nodes.contains(model.node_name) &&
                   changed.commands.exists(snapshot.node.commands.contains)))
                overview.delay_repaint.invoke()

              val visible_lines = text_area.getVisibleLines
              if (visible_lines > 0) {
                if (changed.assignment || load_changed)
                  text_area.invalidateScreenLineRange(0, visible_lines)
                else {
                  val visible_range = JEdit_Lib.visible_range(text_area).get
                  val visible_iterator =
                    snapshot.node.command_iterator(snapshot.revert(visible_range)).map(_._1)
                  if (visible_iterator.exists(changed.commands)) {
                    for {
                      line <- (0 until visible_lines).iterator
                      start = text_area.getScreenLineStartOffset(line) if start >= 0
                      end = text_area.getScreenLineEndOffset(line) if end >= 0
                      range = Text.Range(start, end)
                      line_cmds = snapshot.node.command_iterator(snapshot.revert(range)).map(_._1)
                      if line_cmds.exists(changed.commands)
                    } text_area.invalidateScreenLineRange(line, line)
                  }
                }
              }
            }
          }
        }
    }


  /* activation */

  private def activate()
  {
    val painter = text_area.getPainter

    painter.addExtension(TextAreaPainter.LOWEST_LAYER, update_view)
    rich_text_area.activate()
    text_area.getGutter.addExtension(gutter_painter)
    text_area.addKeyListener(key_listener)
    text_area.addCaretListener(caret_listener)
    text_area.addLeftOfScrollBar(overview)
    Isabelle.structure_matchers(JEdit_Lib.buffer_mode(text_area.getBuffer)).
      foreach(text_area.addStructureMatcher(_))
    session.raw_edits += main
    session.commands_changed += main
  }

  private def deactivate()
  {
    val painter = text_area.getPainter

    session.raw_edits -= main
    session.commands_changed -= main
    Isabelle.structure_matchers(JEdit_Lib.buffer_mode(text_area.getBuffer)).
      foreach(text_area.removeStructureMatcher(_))
    text_area.removeLeftOfScrollBar(overview); overview.delay_repaint.revoke()
    text_area.removeCaretListener(caret_listener); delay_caret_update.revoke()
    text_area.removeKeyListener(key_listener)
    text_area.getGutter.removeExtension(gutter_painter)
    rich_text_area.deactivate()
    painter.removeExtension(update_view)
  }
}
