/*
 * Dockable window for raw process output
 *
 * @author Fabian Immler, TU Munich
 * @author Johannes Hölzl, TU Munich
 */

package isabelle.jedit


import java.awt.{Dimension, Graphics, GridLayout}
import javax.swing.{JPanel, JTextArea, JScrollPane}

import org.gjt.sp.jedit.View
import org.gjt.sp.jedit.gui.DockableWindowManager


class OutputDockable(view : View, position : String) extends JPanel {

  if (position == DockableWindowManager.FLOATING)
    setPreferredSize(new Dimension(500, 250))

  setLayout(new GridLayout(1, 1))
  add(new JScrollPane(new JTextArea))

  def set_text(output_text_view: JTextArea) {
    removeAll()
    add(new JScrollPane(output_text_view))
    revalidate()
  }
}
