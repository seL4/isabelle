/*  Title:      Pure/General/symbol.scala
    Author:     Fabian Immler, TU Munich
    Author:     Makarius

Delayed action: executed once after specified time span, even if
prodded frequently.
*/

package isabelle

import javax.swing.Timer
import java.awt.event.{ActionListener, ActionEvent}


object Delay
{
  def apply(amount: Int)(action: => Unit) = new Delay(amount)(action)
}

class Delay(amount: Int)(action: => Unit)
{
  private val timer = new Timer(amount,
    new ActionListener { override def actionPerformed(e: ActionEvent) { action } })
  def prod()
  {
    if (!timer.isRunning()) {
      timer.setRepeats(false)
      timer.start()
    }
  }
}
