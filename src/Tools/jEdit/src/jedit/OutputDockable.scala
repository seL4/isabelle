package isabelle.jedit

import java.awt.GridLayout

import javax.swing.{ JPanel, JTextArea, JScrollPane }

import org.gjt.sp.jedit.View

class OutputDockable(view : View, position : String) extends JPanel {

  setLayout(new GridLayout(1, 1))
  add(new JScrollPane(new JTextArea("No Prover running")))
}
