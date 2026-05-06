/*  Title:      Tools/jEdit/src/jedit_accessible.scala
    Author:     Makarius

Support for accessible jEdit components, notably used with screenreaders:
  - NVDA (Windows), see https://www.nvaccess.org
  - JAWS (Windows), see https://support.freedomscientific.com/Downloads/JAWS
  - VoiceOver (macOS), builtin Command-F5
*/

package isabelle.jedit

import scala.language.unsafeNulls

import isabelle._

import org.gjt.sp.jedit
import org.gjt.sp.jedit.{jEdit, Buffer, ViewFactory, TextUtilities, Registers}
import org.gjt.sp.jedit.bufferset.BufferSet
import org.gjt.sp.jedit.buffer.JEditBuffer
import org.gjt.sp.jedit.textarea.{JEditTextArea, JEditTextAreaFactory, TextArea => TextArea_JEdit,
  TextAreaPainter, TextAreaPainterFactory, Selection}

import java.awt.{Point, Rectangle}
import java.text.BreakIterator
import javax.accessibility.{Accessible, AccessibleContext, AccessibleRole, AccessibleText,
  AccessibleEditableText, AccessibleExtendedText, AccessibleState, AccessibleStateSet,
  AccessibleTextSequence}
import javax.swing.{JPanel, SwingUtilities}
import javax.swing.text.{AttributeSet, SimpleAttributeSet, StyleConstants}
import javax.swing.event.{CaretListener, CaretEvent}


object JEdit_Accessible {
  def make_title(prefix: String, jbuffer: JEditBuffer): String = {
    val suffix =
      jbuffer match {
        case buffer: Buffer =>
          if (jEdit.getBooleanProperty("view.showFullPath") && !buffer.isNewFile) {
            buffer.getPath(true)
          }
          else buffer.getName
        case _ => ""
      }
    prefix + if_proper(prefix.nonEmpty && suffix.nonEmpty, " - ") + suffix
  }


  /* view */

  class View_Factory extends ViewFactory {
    override def create(buffer: Buffer, config: jedit.View.ViewConfig): jedit.View =
      new View(buffer, config)
  }

  class View(buffer0: Buffer, config: jedit.View.ViewConfig) extends jedit.View(buffer0, config) {
    override def getAccessibleContext: AccessibleContext = {
      if (accessibleContext == null) { accessibleContext = new Accessible_Context }
      accessibleContext
    }

    class Accessible_Context extends AccessibleJFrame {
      override def getAccessibleName: String = make_title(PIDE.title, getBuffer)
    }
  }


  /* editpane */

  class EditPane_Factory extends jedit.EditPaneFactory {
    override def create(view: jedit.View, bufferSetSource: BufferSet, buffer: Buffer): jedit.EditPane =
      new EditPane(view, bufferSetSource, buffer)
  }

  class EditPane(view: jedit.View, bufferSetSource: BufferSet, buffer0: Buffer)
      extends jedit.EditPane(view: jedit.View, bufferSetSource: BufferSet, buffer0: Buffer) {
    override def getAccessibleContext: AccessibleContext = {
      if (accessibleContext == null) { accessibleContext = new Accessible_Context }
      accessibleContext
    }

    class Accessible_Context extends AccessibleJPanel {
      override def getAccessibleName: String = make_title("editor panel", getBuffer)
    }
  }


  /* textarea */

  def attributes(
    bold: Boolean = false,
    italic: Boolean = false,
    underline: Boolean = false
  ): AttributeSet = {
    if (bold || italic || underline) {
      val atts = new SimpleAttributeSet
      if (bold) StyleConstants.setBold(atts, true)
      if (italic) StyleConstants.setItalic(atts, true)
      if (underline) StyleConstants.setUnderline(atts, true)
      atts
    }
    else SimpleAttributeSet.EMPTY
  }

  class TextArea_Factory extends JEditTextAreaFactory {
    override def create(view: jedit.View): JEditTextArea = new TextArea(view)
  }

  class TextArea(view: jedit.View) extends JEditTextArea(view: jedit.View) {
    text_area =>

    def accessible_text_changed(offset: Text.Offset = 0): Unit = GUI_Thread.require {
      accessibleContext match {
        case accessible_context: Accessible_Context => accessible_context.text_changed(offset)
        case _ =>
      }
    }

    override def getAccessibleContext: Accessible_Context =
      accessibleContext match {
        case accessible_context: Accessible_Context => accessible_context
        case _ =>
          val accessible_context = new Accessible_Context
          accessibleContext = accessible_context
          text_area.addCaretListener(accessible_context)
          accessible_context
      }

    protected class Accessible_Context
    extends AccessibleJPanel with AccessibleEditableText with AccessibleExtendedText
      with CaretListener {
      override def getAccessibleText: AccessibleText = this
      override def getAccessibleEditableText: AccessibleEditableText = this

      override def getAccessibleName: String = make_title("editor text", buffer)
      override def getAccessibleRole: AccessibleRole = AccessibleRole.TEXT
      override def getAccessibleStateSet: AccessibleStateSet = {
        val states = super.getAccessibleStateSet
        // see javax.swing.text.JTextComponent.AccessibleJTextComponent
        states.add(AccessibleState.EDITABLE)
        // see javax.swing.JEditorPane.AccessibleJEditorPane
        states.add(AccessibleState.MULTI_LINE)
        states
      }

      def text_changed(offset: Text.Offset): Unit =
        firePropertyChange(AccessibleContext.ACCESSIBLE_TEXT_PROPERTY, null, Value.Int.obj(offset))

      private var old_caret = 0
      override def caretUpdate(e: CaretEvent): Unit = {
        val caret = e.getDot
        if (old_caret != caret) {
          // see javax.swing.text.JTextComponent.AccessibleJTextComponent
          firePropertyChange(AccessibleContext.ACCESSIBLE_CARET_PROPERTY, old_caret, caret)
          old_caret = caret
        }

        for (text <- proper_string(getSelectedText)) {
          // see javax.swing.text.JTextComponent.AccessibleJTextComponent
          firePropertyChange(AccessibleContext.ACCESSIBLE_SELECTION_PROPERTY, null, text)
        }
      }

      private def get_text(range: Text.Range): Option[Text.Info[String]] =
        JEdit_Lib.get_text(buffer, range).map(Text.Info(range, _))

      private def get_character(offset: Text.Offset, inc: Int = 0): Option[Text.Info[String]] =
        JEdit_Lib.buffer_lock(buffer) {
          if (offset < 0 || offset >= buffer.getLength) None
          else {
            val it = JEdit_Lib.grapheme_iterator(getBuffer)
            val i = if (it.isBoundary(offset)) offset else it.preceding(offset)
            if (i == BreakIterator.DONE) None
            else {
              val j = if (inc < 0) it.preceding(i) else it.following(i)
              if (j == BreakIterator.DONE) None
              else {
                if (inc == 0) get_text(Text.Range(i, j))
                else if (inc < 0) get_text(Text.Range(j, i))
                else {
                  val k = it.following(j)
                  if (k == BreakIterator.DONE) None
                  else get_text(Text.Range(j, k))
                }
              }
            }
          }
        }

      private def get_word(offset: Text.Offset, inc: Int = 0): Option[Text.Info[String]] =
        JEdit_Lib.buffer_lock(buffer) {
          val text_length = buffer.getLength
          if (offset < 0 || offset >= text_length) None
          else {
            val text = buffer.getSegment(0, text_length)
            val text_range = Text.Range(0, text_length)

            def word_range(pos: Int): Option[Text.Range] = {
              val a = buffer.getStringProperty("noWordSep")
              val b = text_area.getJoinNonWordChars
              val start = TextUtilities.findWordStart(text, pos, a, b, false, false)
              val stop = TextUtilities.findWordEnd(text, pos + 1, a, b, false, false)
              Text.Range(start, stop).try_restrict(text_range).filterNot(_.is_singularity)
            }

            word_range(offset).flatMap(range =>
              if (inc == 0) get_text(range)
              else if (inc < 0 && range.start > 0) word_range(range.start - 1).flatMap(get_text)
              else if (inc > 0 && range.stop > 0 && range.stop < text_length - 1) {
                word_range(range.stop).flatMap(get_text)
              }
              else None)
          }
        }

      private def get_line(offset: Text.Offset, inc: Int = 0): Option[Text.Info[String]] =
        JEdit_Lib.buffer_lock(buffer) {
          val current =
            try { Some(text_area.getLineOfOffset(offset)) }
            catch { case _: ArrayIndexOutOfBoundsException => None }
          current.flatMap(line =>
            if (inc == 0) Some(line)
            else if (inc < 0 && line > 0) Some(line - 1)
            else if (line < text_area.getLineCount - 1) Some(line + 1)
            else None
          ).flatMap(line => get_text(JEdit_Lib.line_range(buffer, line)))
        }

      private def get_part(part: Int, offset: Text.Offset, inc: Int = 0): Option[Text.Info[String]] =
        part match {
          case AccessibleText.CHARACTER => get_character(offset, inc = inc)
          case AccessibleText.WORD => get_word(offset, inc = inc)
          case AccessibleExtendedText.LINE => get_line(offset, inc = inc)
          case _ => None
        }

      private def get_part_sequence0(part: Int, offset: Text.Offset, inc: Int = 0): AccessibleTextSequence =
        get_part(part, offset, inc = inc) match {
          case Some(res) =>
            new AccessibleTextSequence(res.range.start, res.range.stop, res.info) {
              override def toString: String =
                "AccessibleTextSequence(" + startIndex + ", " + endIndex + ", " + quote(text) +")"
            }
          case None => null
        }

      private def get_part_text0(part: Int, offset: Text.Offset, inc: Int = 0): String =
        get_part(part, offset, inc = inc) match {
          case Some(res) => res.info
          case None => null
        }

      override def getIndexAtPoint(p: Point): Int = {
        val q = SwingUtilities.convertPoint(text_area, p, painter)
        if (q == null) 0 else text_area.xyToOffset(q.x, q.y)
      }

      override def getCharacterBounds(index: Int): Rectangle =
        (for {
          info <- get_character(index)
          gfx <- JEdit_Lib.gfx_range(text_area)(info.range)
        }
        yield {
          val r = new Rectangle(gfx.x, gfx.y, gfx.length, painter.getLineHeight)
          SwingUtilities.convertRectangle(painter, r, text_area)
        }).orNull

      override def getTextBounds(start: Int, end: Int): Rectangle = {
        val rs =
          List.from(
            for {
              index <- (start to end).iterator
              r = getCharacterBounds(index) if r != null
            } yield r)
        if (rs.isEmpty) null
        else {
          val x1 = rs.iterator.map(_.x).min
          val y1 = rs.iterator.map(_.y).min
          val x2 = rs.iterator.map(r => r.x + r.width).max
          val y2 = rs.iterator.map(r => r.y + r.height).max
          new Rectangle(x1, y1, x2 - x1, y2 - y1)
        }
      }

      override def getCharCount: Int = text_area.getBufferLength

      override def getCaretPosition: Int = text_area.getCaretPosition

      override def getTextSequenceAt(part: Int, index: Int): AccessibleTextSequence =
        get_part_sequence0(part, index)

      override def getTextSequenceAfter(part: Int, index: Int): AccessibleTextSequence =
        get_part_sequence0(part, index, inc = 1)

      override def getTextSequenceBefore(part: Int, index: Int): AccessibleTextSequence =
        get_part_sequence0(part, index, inc = -1)

      override def getAtIndex(part: Int, index: Int): String =
        get_part_text0(part, index)

      override def getAfterIndex(part: Int, index: Int): String =
        get_part_text0(part, index, inc = 1)

      override def getBeforeIndex(part: Int, index: Int): String =
        get_part_text0(part, index, inc = -1)

      override def getTextRange(start: Int, end: Int): String =
        JEdit_Lib.get_text(buffer, Text.Range(start, end + 1)).orNull

      override def getCharacterAttribute(i: Int): AttributeSet =
        PIDE.maybe_rendering(view = Some(view)) match {
          case Some(rendering) if !rendering.snapshot.is_outdated &&
            rendering.hyperlink(Text.Range(i, i + 1)).isDefined => attributes(underline = true)
          case _ => attributes()
        }

      override def setAttributes(start: Int, end: Int, atts: AttributeSet): Unit = {}

      // approximate Java Swing selection: start == end means no selection, just cursor
      override def getSelectionStart: Int =
        JEdit_Lib.selection_range(text_area, getCaretPosition) match {
          case None => getCaretPosition
          case Some(r) => r.start
        }
      override def getSelectionEnd: Int =
        JEdit_Lib.selection_range(text_area, getCaretPosition) match {
          case None => getCaretPosition
          case Some(r) => r.stop
        }
      override def getSelectedText: String =
        JEdit_Lib.buffer_lock(buffer) {
          (for {
            r <- JEdit_Lib.selection_range(text_area, getCaretPosition)
            s <- JEdit_Lib.get_text(buffer, r)
          } yield s).orNull
        }

      override def selectText(start: Int, end: Int): Unit =
        if (!buffer.isReadOnly) {
          text_area.selectNone()
          text_area.addToSelection(new Selection.Range(start, end + 1))
        }

      override def cut(start: Int, end: Int): Unit =
        if (!buffer.isReadOnly) {
          selectText(start, end)
          Registers.cut(text_area, '$')
        }

      override def paste(start: Int): Unit =
        if (!buffer.isReadOnly) {
          selectText(start, start)
          Registers.paste(text_area, '$')
        }

      override def delete(start: Int, end: Int): Unit =
        if (!buffer.isReadOnly) {
          selectText(start, end)
          buffer.remove(start, end + 1 - start)
        }

      override def setTextContents(s: String): Unit =
        if (!buffer.isReadOnly) {
          JEdit_Lib.buffer_edit(buffer) {
            text_area.selectNone()
            buffer.remove(0, buffer.getLength)
            buffer.insert(0, s)
          }
        }

      override def insertTextAtIndex(start: Int, s: String): Unit =
        if (!buffer.isReadOnly) {
          JEdit_Lib.buffer_edit(buffer) {
            selectText(start, start)
            buffer.insert(start, s)
          }
        }

      override def replaceText(start: Int, end: Int, s: String): Unit =
        if (!buffer.isReadOnly) {
          JEdit_Lib.buffer_edit(buffer) {
            selectText(start, end)
            buffer.remove(start, end + 1 - start)
            buffer.insert(start, s)
          }
        }
    }
  }


  /* text area painter */

  class Painter_Factory extends TextAreaPainterFactory {
    override def create(text_area: TextArea_JEdit): TextAreaPainter = new Painter(text_area)
  }

  class Painter(text_area: TextArea_JEdit) extends TextAreaPainter(text_area) {
    override def getAccessibleContext: AccessibleContext = {
      if (accessibleContext == null) {
        accessibleContext = new Accessible_Context
      }
      accessibleContext
    }

    class Accessible_Context extends AccessibleJComponent {
      override def getAccessibleName: String = "editor painter (internal)"
      override def getAccessibleRole: AccessibleRole = AccessibleRole.PANEL
    }
  }
}
