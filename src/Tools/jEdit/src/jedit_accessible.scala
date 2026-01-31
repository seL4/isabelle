/*  Title:      Tools/jEdit/src/jedit_accessible.scala
    Author:     Makarius

Support for accessible jEdit components, notably used with screenreaders:
  - NVDA (Windows), see https://www.nvaccess.org
  - JAWS (Windows), see https://support.freedomscientific.com/Downloads/JAWS
  - VoiceOver (macOS), builtin Command-F5
*/

package isabelle.jedit


import isabelle._

import org.gjt.sp.jedit
import org.gjt.sp.jedit.{jEdit, Buffer, ViewFactory, TextUtilities, Registers}
import org.gjt.sp.jedit.bufferset.BufferSet
import org.gjt.sp.jedit.buffer.JEditBuffer
import org.gjt.sp.jedit.textarea.{JEditTextArea, JEditTextAreaFactory, TextArea => TextArea_JEdit,
  TextAreaPainter, TextAreaPainterFactory, Selection}

import java.awt.{Point, Rectangle}
import javax.accessibility.{Accessible, AccessibleContext, AccessibleRole, AccessibleText,
  AccessibleEditableText, AccessibleState, AccessibleStateSet}
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

    override def getAccessibleContext: AccessibleContext = {
      if (accessibleContext == null) {
        val accessible_context = new Accessible_Context
        text_area.addCaretListener(accessible_context)
        accessibleContext = accessible_context
      }
      accessibleContext
    }

    protected class Accessible_Context extends AccessibleJPanel with CaretListener {
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
      override def getAccessibleText: AccessibleText = accessible_text
      override def getAccessibleEditableText: AccessibleEditableText = accessible_text
      override def getAccessibleChildrenCount: Int = 0
      override def getAccessibleChild(i: Int): Accessible = null

      private var old_caret = 0
      override def caretUpdate(e: CaretEvent): Unit = {
        val caret = e.getDot
        if (old_caret != caret) {
          // see javax.swing.text.JTextComponent.AccessibleJTextComponent
          firePropertyChange(AccessibleContext.ACCESSIBLE_CARET_PROPERTY, old_caret, caret)
          old_caret = caret
        }
      }
    }

    protected val accessible_text: AccessibleEditableText = new Accessible_Text

    protected class Accessible_Text extends AccessibleEditableText {
      private def get_text(range: Text.Range): Option[Text.Info[String]] =
        JEdit_Lib.get_text(buffer, range).map(Text.Info(range, _))

      private def get_character(offset: Text.Offset, inc: Int = 0): Option[Text.Info[String]] =
        JEdit_Lib.buffer_lock(buffer) {
          if (offset < 0 || offset >= buffer.getLength) None
          else {
            val breaker = new TextArea_JEdit.LineCharacterBreaker(text_area, offset)
            val i = if (breaker.offsetIsBoundary(offset)) offset else breaker.previousOf(offset)
            val range =
              if (inc == 0) Text.Range(i, breaker.nextOf(i))
              else if (inc < 0) Text.Range(breaker.previousOf(i), i)
              else {
                val j = breaker.nextOf(i)
                Text.Range(j, breaker.nextOf(j))
              }
            get_text(range)
          }
        }

      private def get_word(offset: Text.Offset, inc: Int = 0): Option[String] =
        JEdit_Lib.buffer_lock(buffer) {
          if (offset < 0 || offset >= buffer.getLength) None
          else {
            val line = text_area.getLineOfOffset(offset)
            val line1 = if (line > 0) line - 1 else line
            val line2 = if (line < text_area.getLineCount - 1) line + 1 else line

            val text_start = text_area.getLineStartOffset(line1)
            val text_stop = text_area.getLineEndOffset(line2)
            val text = text_area.getText(text_start, text_stop - text_start)

            def word_range(pos: Int): Text.Range = {
              val a = buffer.getStringProperty("noWordSep")
              val b = text_area.getJoinNonWordChars
              val start = TextUtilities.findWordStart(text, pos - text_start, a, b, false, false)
              val stop = TextUtilities.findWordEnd(text, pos - text_start + 1, a, b, false, false)
              Text.Range(start + text_start, stop + text_start)
            }

            val range = word_range(offset)
            val result =
              if (inc == 0) get_text(range)
              else if (inc < 0 && range.start > 0) get_text(word_range(range.start - 1))
              else if (inc > 0 && range.stop > 0 && range.stop < buffer.getLength - 1) {
                get_text(word_range(range.stop))
              }
              else None
            result.map(info =>
              cat_lines(
                split_lines(info.info)
                  .reverse.dropWhile(_.isEmpty)
                  .reverse.dropWhile(_.isEmpty)))
          }
        }

      override def getIndexAtPoint(p: Point): Int = {
        val q = SwingUtilities.convertPoint(text_area, p, painter)
        text_area.xyToOffset(q.x, q.y)
      }

      override def getCharacterBounds(index: Int): Rectangle =
        (for {
          info <- get_character(index)
          gfx <- JEdit_Lib.gfx_range(text_area)(info.range)
        }
        yield {
          val r = new Rectangle(gfx.x, gfx.y, gfx.length, painter.getLineHeight)
          SwingUtilities.convertRectangle(painter, r, text_area)
        }).getOrElse(new Rectangle())

      override def getCharCount: Int = text_area.getBufferLength

      override def getCaretPosition: Int = text_area.getCaretPosition

      override def getAtIndex(part: Int, index: Int): String =
        part match {
          case AccessibleText.CHARACTER => get_character(index).map(_.info).orNull
          case AccessibleText.WORD => get_word(index).orNull
          case _ => null
        }

      override def getAfterIndex(part: Int, index: Int): String =
        part match {
          case AccessibleText.CHARACTER => get_character(index, inc = 1).map(_.info).orNull
          case AccessibleText.WORD => get_word(index, inc = 1).orNull
          case _ => null
        }

      override def getBeforeIndex(part: Int, index: Int): String =
        part match {
          case AccessibleText.CHARACTER => get_character(index, inc = -1).map(_.info).orNull
          case AccessibleText.WORD => get_word(index, inc = -1).orNull
          case _ => null
        }

      override def getTextRange(start: Int, stop: Int): String =
        JEdit_Lib.get_text(buffer, Text.Range(start min stop, start max stop)).orNull

      override def getCharacterAttribute(i: Int): AttributeSet =
        PIDE.maybe_rendering(view) match {
          case Some(rendering) if !rendering.snapshot.is_outdated &&
            rendering.hyperlink(Text.Range(i, i + 1)).isDefined => attributes(underline = true)
          case _ => attributes()
        }

      override def setAttributes(start: Int, stop: Int, atts: AttributeSet): Unit = {}

      override def getSelectionStart: Int =
        if (text_area.getSelectionCount == 1) text_area.getSelection(0).getStart
        else -1

      override def getSelectionEnd: Int =
        if (text_area.getSelectionCount == 1) text_area.getSelection(0).getEnd
        else -1

      override def getSelectedText: String =
        if (text_area.getSelectionCount == 1) {
          val start = getSelectionStart
          val stop = getSelectionEnd
          buffer.getText(start, stop - start)
        }
        else ""

      override def selectText(start: Int, stop: Int): Unit =
        if (!buffer.isReadOnly) {
          text_area.selectNone()
          text_area.addToSelection(new Selection.Range(start min stop, start max stop))
        }

      override def cut(start: Int, stop: Int): Unit =
        if (!buffer.isReadOnly) {
          selectText(start, stop)
          Registers.cut(text_area, '$')
        }

      override def paste(start: Int): Unit =
        if (!buffer.isReadOnly) {
          selectText(start, start)
          Registers.paste(text_area, '$')
        }

      override def delete(start: Int, stop: Int): Unit =
        if (!buffer.isReadOnly) {
          selectText(start, stop)
          buffer.remove(start min stop, (stop - start).abs)
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

      override def replaceText(start: Int, stop: Int, s: String): Unit =
        if (!buffer.isReadOnly) {
          JEdit_Lib.buffer_edit(buffer) {
            selectText(start, stop)
            buffer.remove(start min stop, (start - stop).abs)
            buffer.insert(start min stop, s)
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
    }
  }
}
