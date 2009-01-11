/*
 * Editor pane for plugin options
 *
 * @author Johannes Hölzl, TU Munich
 */

package isabelle.jedit

import java.lang.Integer

import java.awt.BorderLayout
import java.awt.GridBagConstraints.HORIZONTAL
import java.awt.BorderLayout.{ WEST, CENTER, EAST }
import java.awt.event.{ ActionListener, ActionEvent }
import javax.swing.{ JTextField, JButton, JPanel, JLabel, JFileChooser, 
                     JSpinner, SwingUtilities, JComboBox }

import org.gjt.sp.jedit.AbstractOptionPane


class OptionPane extends AbstractOptionPane("isabelle") {
  var pathName = new JTextField()
  var fontSize = new JSpinner()
  var logicName = new JComboBox()
    
  override def _init() {
    addComponent(Isabelle.Property("font-path.title"), {
      val pickPath = new JButton("...")
      pickPath.addActionListener(new ActionListener() {
        override def actionPerformed(e : ActionEvent) {
          val chooser = new JFileChooser(pathName.getText())
          if (chooser.showOpenDialog(OptionPane.this) == JFileChooser.APPROVE_OPTION)
            pathName.setText(chooser.getSelectedFile().getAbsolutePath())
        } 
      })

      pathName.setText(Isabelle.Property("font-path"))
      
      val pathPanel = new JPanel(new BorderLayout())
      pathPanel.add(pathName, CENTER)
      pathPanel.add(pickPath, EAST)
      pathPanel
    }, HORIZONTAL)

    addComponent(Isabelle.Property("font-size.title"), {
      try {
        if (Isabelle.Property("font-size") != null)
          fontSize.setValue(Integer.valueOf(Isabelle.Property("font-size")))
      }
      catch {
        case e : NumberFormatException => 
          fontSize.setValue(14)
      }
      
      fontSize
    })

    addComponent(Isabelle.Property("logic.title"), {
      for (name <- Isabelle.system.find_logics()) {
        logicName.addItem(name)
        if (name == Isabelle.Property("logic"))
          logicName.setSelectedItem(name)
      }

      logicName
    })
  }
    
  override def _save() {
    val size = fontSize.getValue()
    val name = pathName.getText()
    if (Isabelle.Property("font-path") != name || Isabelle.Property("font-size") != size.toString) {
      Isabelle.Property("font-path") = name
      Isabelle.Property("font-size") = size.toString
      SwingUtilities invokeLater new Runnable() {
        override def run() = 
          Isabelle.plugin.set_font(name, size.asInstanceOf[Integer].intValue)
      }
    }
    
    val logic = logicName.getSelectedItem.asInstanceOf[String]
    Isabelle.Property("logic") = logic
  }
}
