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

import isabelle.IsabelleSystem

import org.gjt.sp.jedit.AbstractOptionPane

class OptionPane extends AbstractOptionPane("isabelle") {
  import Plugin.property
  
  var pathName = new JTextField()
  var fontSize = new JSpinner()
  var logicName = new JComboBox()
    
  override def _init() {
    addComponent(property("font-path.title"), {
      val pickPath = new JButton("...")
      pickPath.addActionListener(new ActionListener() {
        override def actionPerformed(e : ActionEvent) {
          val chooser = new JFileChooser(pathName.getText())
          if (chooser.showOpenDialog(OptionPane.this) == JFileChooser.APPROVE_OPTION)
            pathName.setText(chooser.getSelectedFile().getAbsolutePath())
        } 
      })

      pathName.setText(property("font-path"))
      
      val pathPanel = new JPanel(new BorderLayout())
      pathPanel.add(pathName, CENTER)
      pathPanel.add(pickPath, EAST)
      pathPanel
    }, HORIZONTAL)

    addComponent(property("font-size.title"), {
      try {
        if (property("font-size") != null)
          fontSize.setValue(Integer.valueOf(property("font-size")))
      }
      catch {
        case e : NumberFormatException => 
          fontSize.setValue(14)
      }
      
      fontSize
    })

    addComponent(property("logic.title"), {
      val logics : Array[Object] = 
        (IsabelleSystem.isabelle_tool("findlogics") _1).split("\\s").asInstanceOf[Array[Object]]
      for (name <- logics) {
        logicName.addItem(name)
        if (name == property("logic"))
          logicName.setSelectedItem(name)
      }
      
      logicName
    })
  }
    
  override def _save() {
    val size = fontSize.getValue()
    val name = pathName.getText()
    if (property("font-path") != name || property("font-size") != size.toString) {
      property("font-path", name)
      property("font-size", size.toString)
      SwingUtilities invokeLater new Runnable() {
        override def run() = 
          Plugin.plugin.setFont(name, size.asInstanceOf[Integer].intValue)
      }
    }
    
    val logic = logicName.getSelectedItem.asInstanceOf[String]
    property("logic", logic) 
  }
}
