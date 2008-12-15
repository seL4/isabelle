package isabelle.utils

import javax.swing.Timer
import java.awt.event.{ActionListener, ActionEvent}

class Delay(amount : Int, action : () => Unit) {

  val timer : Timer = new Timer(amount, new ActionListener {
      override def actionPerformed(e:ActionEvent){
        action ()
      }
    })
  // if called very often, action is executed at most once
  // in amount milliseconds
  def delay_or_ignore () = {
    if (! timer.isRunning()){
      timer.setRepeats(false)
      timer.start()
    }
  }
}
