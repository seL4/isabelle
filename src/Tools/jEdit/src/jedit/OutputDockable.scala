package isabelle.jedit

import java.awt.GridLayout

import javax.swing.{ JPanel, JTextArea, JScrollPane }

import org.gjt.sp.jedit.View

class OutputDockable(view : View, position : String) extends JPanel {
  {
    val textView = new JTextArea()
    
    setLayout(new GridLayout(1, 1))
    add(new JScrollPane(textView))
    
    textView.append("== Isabelle output ==\n")
    
    Plugin.plugin.prover.outputInfo.add( text => textView.append(text) )
  }
}
