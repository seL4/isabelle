/*  Title:      Tools/jEdit/src/document_view.scala
    Author:     Fabian Immler, TU Munich
    Author:     Makarius

Document view connected to jEdit text area.
*/

package isabelle.jedit


import isabelle._

import scala.collection.mutable
import scala.collection.immutable.SortedMap
import scala.actors.Actor._

import java.lang.System
import java.text.BreakIterator
import java.awt.{Color, Graphics2D, Point}
import javax.swing.event.{CaretListener, CaretEvent}

import org.gjt.sp.jedit.{jEdit, Debug}
import org.gjt.sp.jedit.gui.RolloverButton
import org.gjt.sp.jedit.options.GutterOptionPane
import org.gjt.sp.jedit.textarea.{JEditTextArea, TextArea, TextAreaExtension, TextAreaPainter}
import org.gjt.sp.jedit.syntax.{SyntaxStyle}


object Document_View
{
  /* document view of text area */

  private val key = new Object

  def apply(text_area: JEditTextArea): Option[Document_View] =
  {
    Swing_Thread.require()
    text_area.getClientProperty(key) match {
      case doc_view: Document_View => Some(doc_view)
      case _ => None
    }
  }

  def exit(text_area: JEditTextArea)
  {
    Swing_Thread.require()
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

  def get_rendering(): Isabelle_Rendering =
    Isabelle_Rendering(model.snapshot(), Isabelle.options.value)

  val rich_text_area = new Rich_Text_Area(text_area.getView, text_area, get_rendering _)


  /* perspective */

  def perspective(): Text.Perspective =
  {
    Swing_Thread.require()
    val buffer_range = model.buffer_range()
    Text.Perspective(
      for {
        i <- 0 until text_area.getVisibleLines
        start = text_area.getScreenLineStartOffset(i)
        stop = text_area.getScreenLineEndOffset(i)
        if start >= 0 && stop >= 0
        range <- buffer_range.try_restrict(Text.Range(start, stop))
        if !range.is_singularity
      }
      yield range)
  }

  private def update_perspective = new TextAreaExtension
  {
    override def paintScreenLineRange(gfx: Graphics2D,
      first_line: Int, last_line: Int, physical_lines: Array[Int],
      start: Array[Int], end: Array[Int], y: Int, line_height: Int)
    {
      model.update_perspective()
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
        Swing_Thread.assert()

        val gutter = text_area.getGutter
        val width = GutterOptionPane.getSelectionAreaWidth
        val border_width = jEdit.getIntegerProperty("view.gutter.borderWidth", 3)
        val FOLD_MARKER_SIZE = 12

        if (gutter.isSelectionAreaEnabled && !gutter.isExpanded && width >= 12 && line_height >= 12) {
          val buffer = model.buffer
          JEdit_Lib.buffer_lock(buffer) {
            val rendering = get_rendering()

            for (i <- 0 until physical_lines.length) {
              if (physical_lines(i) != -1) {
                val line_range = JEdit_Lib.proper_line_range(buffer, start(i), end(i))

                // gutter icons
                rendering.gutter_message(line_range) match {
                  case Some(icon) =>
                    val x0 = (FOLD_MARKER_SIZE + width - border_width - icon.getIconWidth) max 10
                    val y0 = y + i * line_height + (((line_height - icon.getIconHeight) / 2) max 0)
                    icon.paintIcon(gutter, gfx, x0, y0)
                  case None =>
                }
              }
            }
          }
        }
      }
    }
  }


  /* caret handling */

  private val delay_caret_update =
    Swing_Thread.delay_last(Time.seconds(Isabelle.options.real("editor_input_delay"))) {
      session.caret_focus.event(Session.Caret_Focus)
    }

  private val caret_listener = new CaretListener {
    override def caretUpdate(e: CaretEvent) { delay_caret_update.invoke() }
  }


  /* text status overview left of scrollbar */

  private object overview extends Text_Overview(this)
  {
    val delay_repaint =
      Swing_Thread.delay_first(
        Time.seconds(Isabelle.options.real("editor_update_delay"))) { repaint() }
  }


  /* main actor */

  private val main_actor = actor {
    loop {
      react {
        case _: Session.Raw_Edits =>
          Swing_Thread.later {
            overview.delay_repaint.postpone(
              Time.seconds(Isabelle.options.real("editor_input_delay")))
          }

        case changed: Session.Commands_Changed =>
          val buffer = model.buffer
          Swing_Thread.later {
            JEdit_Lib.buffer_lock(buffer) {
              if (model.buffer == text_area.getBuffer) {
                val snapshot = model.snapshot()

                if (changed.assignment ||
                    (changed.nodes.contains(model.name) &&
                     changed.commands.exists(snapshot.node.commands.contains)))
                  Swing_Thread.later { overview.delay_repaint.invoke() }

                JEdit_Lib.visible_range(text_area) match {
                  case Some(visible) =>
                    if (changed.assignment) JEdit_Lib.invalidate_range(text_area, visible)
                    else {
                      val visible_cmds =
                        snapshot.node.command_range(snapshot.revert(visible)).map(_._1)
                      if (visible_cmds.exists(changed.commands)) {
                        for {
                          line <- 0 until text_area.getVisibleLines
                          start = text_area.getScreenLineStartOffset(line) if start >= 0
                          end = text_area.getScreenLineEndOffset(line) if end >= 0
                          range = JEdit_Lib.proper_line_range(buffer, start, end)
                          line_cmds = snapshot.node.command_range(snapshot.revert(range)).map(_._1)
                          if line_cmds.exists(changed.commands)
                        } text_area.invalidateScreenLineRange(line, line)
                      }
                    }
                  case None =>
                }
              }
            }
          }

        case bad => System.err.println("command_change_actor: ignoring bad message " + bad)
      }
    }
  }


  /* activation */

  private def activate()
  {
    val painter = text_area.getPainter

    painter.addExtension(TextAreaPainter.LOWEST_LAYER, update_perspective)
    rich_text_area.activate()
    text_area.getGutter.addExtension(gutter_painter)
    text_area.addCaretListener(caret_listener)
    text_area.addLeftOfScrollBar(overview)
    session.raw_edits += main_actor
    session.commands_changed += main_actor
  }

  private def deactivate()
  {
    val painter = text_area.getPainter

    session.raw_edits -= main_actor
    session.commands_changed -= main_actor
    text_area.removeCaretListener(caret_listener); delay_caret_update.revoke()
    text_area.removeLeftOfScrollBar(overview); overview.delay_repaint.revoke()
    text_area.getGutter.removeExtension(gutter_painter)
    rich_text_area.deactivate()
    painter.removeExtension(update_perspective)
  }
}
