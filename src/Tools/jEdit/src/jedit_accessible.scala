/*  Title:      Tools/jEdit/src/jedit_accessible.scala
    Author:     Makarius

Support for accessible jEdit components, notably used with screenreaders:
  - Windows: NVDA (see https://www.nvaccess.org)
  - macOS: VoiceOver (builtin Command-F5)
*/

package isabelle.jedit


import isabelle._

import org.gjt.sp.jedit
import org.gjt.sp.jedit.{Buffer, View}
import org.gjt.sp.jedit.bufferset.BufferSet
import org.gjt.sp.jedit.textarea.{JEditTextArea, JEditTextAreaFactory}

import javax.accessibility.{AccessibleContext, AccessibleRole}
import javax.swing.JPanel


object JEdit_Accessible {
  /* editpane */

  class EditPane_Factory extends jedit.EditPaneFactory {
    override def create(view: View, bufferSetSource: BufferSet, buffer: Buffer): jedit.EditPane =
      new EditPane(view, bufferSetSource, buffer)
  }

  class EditPane(view: View, bufferSetSource: BufferSet, buffer: Buffer)
      extends jedit.EditPane(view: View, bufferSetSource: BufferSet, buffer: Buffer) {
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
    override def create(view: View): JEditTextArea = new TextArea(view)
  }

  class TextArea(view: View) extends JEditTextArea(view: View) {
    override def getAccessibleContext: AccessibleContext = {
      if (accessibleContext == null) { accessibleContext = new Accessible_Context }
      accessibleContext
    }

    class Accessible_Context extends AccessibleJPanel {
      override def getAccessibleName: String = "editor text"
    }
  }
}
