/*  Title:      lib/jedit/plugin/isabelle_dock.scala
    ID:         $Id$
    Author:     Makarius

Dockable window for Isabelle process control.
*/

package isabelle.jedit

import org.gjt.sp.jedit.View
import org.gjt.sp.jedit.gui.DefaultFocusComponent
import org.gjt.sp.jedit.gui.DockableWindowManager
import org.gjt.sp.jedit.gui.RolloverButton
import org.gjt.sp.jedit.gui.HistoryTextField
import org.gjt.sp.jedit.GUIUtilities

import java.awt.Color
import java.awt.Insets
import java.awt.BorderLayout
import java.awt.Dimension
import java.awt.event.ActionListener
import java.awt.event.ActionEvent
import javax.swing.BoxLayout
import javax.swing.JPanel
import javax.swing.JScrollPane
import javax.swing.JTextPane
import javax.swing.text.{StyledDocument, StyleConstants}
import javax.swing.SwingUtilities
import javax.swing.Icon
import javax.swing.Box
import javax.swing.JTextField
import javax.swing.JComboBox
import javax.swing.DefaultComboBoxModel


class IsabelleDock(view: View, position: String)
    extends JPanel(new BorderLayout) with DefaultFocusComponent
{
  private val text = new HistoryTextField("isabelle", false, true)
  private val logicCombo = new JComboBox

  {
    // output pane
    val pane = new JTextPane
    pane.setEditable(false)
    add(BorderLayout.CENTER, new JScrollPane(pane))
    if (position == DockableWindowManager.FLOATING)
      setPreferredSize(new Dimension(1000, 500))

    val doc = pane.getDocument.asInstanceOf[StyledDocument]

    def makeStyle(name: String, bg: Boolean, color: Color) = {
      val style = doc.addStyle(name, null)
      if (bg) StyleConstants.setBackground(style, color)
      else StyleConstants.setForeground(style, color)
      style
    }
    val rawStyle = makeStyle("raw", false, Color.GRAY)
    val infoStyle = makeStyle("info", true, new Color(160, 255, 160))
    val warningStyle = makeStyle("warning", true, new Color(255, 255, 160))
    val errorStyle = makeStyle("error", true, new Color(255, 160, 160))

    IsabellePlugin.addPermanentConsumer (result =>
      if (result != null && !result.is_system) {
        SwingUtilities.invokeLater(new Runnable {
          def run = {
            val logic = IsabellePlugin.isabelle.session
            logicCombo.setModel(new DefaultComboBoxModel(Array(logic).asInstanceOf[Array[AnyRef]]))
            logicCombo.setPrototypeDisplayValue("AAAA")  // FIXME ??

            val doc = pane.getDocument.asInstanceOf[StyledDocument]
            val style = result.kind match {
              case IsabelleProcess.Kind.WARNING => warningStyle
              case IsabelleProcess.Kind.ERROR => errorStyle
              case IsabelleProcess.Kind.TRACING => infoStyle
              case _ => if (result.is_raw) rawStyle else null
            }
            doc.insertString(doc.getLength, IsabellePlugin.result_content(result), style)
            if (!result.is_raw) doc.insertString(doc.getLength, "\n", style)
            pane.setCaretPosition(doc.getLength)
          }
        })
      })


    // control box
    val box = new Box(BoxLayout.X_AXIS)
    add(BorderLayout.SOUTH, box)


    // logic combo
    logicCombo.setToolTipText("Isabelle logics")
    logicCombo.setRequestFocusEnabled(false)
    logicCombo.setModel(new DefaultComboBoxModel(Array("default").asInstanceOf[Array[AnyRef]]))
    box.add(logicCombo)


    // mode combo
    val modeIsar = "Isar"
    val modeML = "ML"
    val modes = Array(modeIsar, modeML)
    var mode = modeIsar

    val modeCombo = new JComboBox
    modeCombo.setToolTipText("Toplevel mode")
    modeCombo.setRequestFocusEnabled(false)
    modeCombo.setModel(new DefaultComboBoxModel(modes.asInstanceOf[Array[AnyRef]]))
    modeCombo.setPrototypeDisplayValue("AAAA")
    modeCombo.addActionListener(new ActionListener {
      def actionPerformed(evt: ActionEvent): Unit = {
        mode = modeCombo.getSelectedItem.asInstanceOf[String]
      }
    })
    box.add(modeCombo)


    // input field
    text.setToolTipText("Command line")
    text.addActionListener(new ActionListener {
      def actionPerformed(evt: ActionEvent): Unit = {
        val command = text.getText
        if (command.length > 0) {
          if (mode == modeIsar)
            IsabellePlugin.isabelle.command(command)
          else if (mode == modeML)
            IsabellePlugin.isabelle.ML(command)
          text.setText("")
        }
      }
    })
    box.add(text)


    // buttons
    def iconButton(icon: String, tip: String, action: => Unit) = {
      val button = new RolloverButton(GUIUtilities.loadIcon(icon))
      button.setToolTipText(tip)
      button.setMargin(new Insets(0,0,0,0))
      button.setRequestFocusEnabled(false)
      button.addActionListener(new ActionListener {
        def actionPerformed(evt: ActionEvent): Unit = action
      })
      box.add(button)
    }

    iconButton("Cancel.png", "Stop", IsabellePlugin.isabelle.interrupt)
    iconButton("Clear.png", "Clear", pane.setText(""))
  }

  def focusOnDefaultComponent: Unit = text.requestFocus
}

