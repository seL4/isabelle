/*  Title:      Tools/jEdit/src/jedit_accessible.scala
    Author:     Makarius

Support for accessible jEdit components, notably used with screenreaders:
  - Windows: NVDA (see https://www.nvaccess.org)
  - macOS: VoiceOver (builtin Command-F5)
*/

package isabelle.jedit


import isabelle._

import org.gjt.sp.jedit
import org.gjt.sp.jedit.{Buffer, ViewFactory}
import org.gjt.sp.jedit.bufferset.BufferSet
import org.gjt.sp.jedit.textarea.{JEditTextArea, JEditTextAreaFactory, TextArea => TextArea_JEdit,
  TextAreaPainter, TextAreaPainterFactory}

import java.awt.{Point, Rectangle}
import javax.accessibility.{Accessible, AccessibleContext, AccessibleRole, AccessibleText}
import javax.swing.{JPanel, SwingUtilities}
import javax.swing.text.{AttributeSet, SimpleAttributeSet}


object JEdit_Accessible {
  /* view */

  class View_Factory extends ViewFactory {
    override def create(buffer: Buffer, config: jedit.View.ViewConfig): jedit.View =
      new View(buffer, config)
  }

  class View(buffer: Buffer, config: jedit.View.ViewConfig) extends jedit.View(buffer, config) {
    override def getAccessibleContext: AccessibleContext = {
      if (accessibleContext == null) { accessibleContext = new Accessible_Context }
      accessibleContext
    }

    class Accessible_Context extends AccessibleJFrame {
    }
  }


  /* editpane */

  class EditPane_Factory extends jedit.EditPaneFactory {
    override def create(view: jedit.View, bufferSetSource: BufferSet, buffer: Buffer): jedit.EditPane =
      new EditPane(view, bufferSetSource, buffer)
  }

  class EditPane(view: jedit.View, bufferSetSource: BufferSet, buffer: Buffer)
      extends jedit.EditPane(view: jedit.View, bufferSetSource: BufferSet, buffer: Buffer) {
    override def getAccessibleContext: AccessibleContext = {
      if (accessibleContext == null) { accessibleContext = new Accessible_Context }
      accessibleContext
    }

    class Accessible_Context extends AccessibleJPanel {
      override def getAccessibleName: String = "editor panel"
    }
  }


  /* textarea */

  class TextArea_Factory extends JEditTextAreaFactory {
    override def create(view: jedit.View): JEditTextArea = new TextArea(view)
  }

  class TextArea(view: jedit.View) extends JEditTextArea(view: jedit.View) {
    text_area =>

    override def getAccessibleContext: AccessibleContext = {
      if (accessibleContext == null) { accessibleContext = new Accessible_Context }
      accessibleContext
    }

    protected class Accessible_Context extends AccessibleJPanel {
      override def getAccessibleName: String = "editor text"
      override def getAccessibleRole: AccessibleRole = AccessibleRole.TEXT
      override def getAccessibleText: AccessibleText = accessible_text
      override def getAccessibleChildrenCount: Int = 0
      override def getAccessibleChild(i: Int): Accessible = null
    }

    protected val accessible_text: AccessibleText = new Accessible_Text

    protected class Accessible_Text extends AccessibleText {
      private def get_character(i: Text.Offset, inc: Int = 0): Option[Text.Info[String]] =
        JEdit_Lib.buffer_lock(buffer) {
          val range0 = JEdit_Lib.point_range(buffer, i)
          val range =
            if (inc == 0) range0
            else JEdit_Lib.point_range(buffer, if (inc > 0) range0.stop else range0.start - 1)
          JEdit_Lib.get_text(buffer, range).map(Text.Info(range, _))
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
          case AccessibleText.CHARACTER =>
            get_character(index).map(_.info).orNull
          case _ => null
        }

      override def getAfterIndex(part: Int, index: Int): String =
        part match {
          case AccessibleText.CHARACTER =>
            get_character(index, inc = 1).map(_.info).orNull
          case _ => null
        }

      override def getBeforeIndex(part: Int, index: Int): String =
        part match {
          case AccessibleText.CHARACTER =>
            get_character(index, inc = -1).map(_.info).orNull
          case _ => null
        }

      override def getCharacterAttribute(i: Int): AttributeSet =
        SimpleAttributeSet.EMPTY

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
