/*  Title:      Tools/jEdit/src/process_indicator.scala
    Author:     Makarius

Process indicator with animated icon.
*/

package isabelle.jedit


import isabelle._

import java.awt.event.{ActionListener, ActionEvent}
import javax.swing.{ImageIcon, Timer}
import scala.swing.{Label, Component}


class Process_Indicator {
  private val label = new Label

  private val passive_icon =
    JEdit_Lib.load_icon(PIDE.options.string("process_passive_icon")).getImage
  private val active_icons =
    space_explode(':', PIDE.options.string("process_active_icons")).map(name =>
      JEdit_Lib.load_icon(name).getImage)

  private class Animation extends ImageIcon(passive_icon) {
    private var current_frame = 0
    private val timer =
      new Timer(0, { (_: ActionEvent) =>
        current_frame = (current_frame + 1) % active_icons.length
        setImage(active_icons(current_frame))
        label.repaint()
      })
    timer.setRepeats(true)

    def update(rate: Int): Unit = {
      if (rate == 0) {
        setImage(passive_icon)
        timer.stop()
        label.repaint()
      }
      else {
        val delay = 1000 / rate
        timer.setInitialDelay(delay)
        timer.setDelay(delay)
        timer.restart()
      }
    }
  }

  private val animation = new Animation
  label.icon = animation

  def component: Component = label

  def update(tip: String, rate: Int): Unit = {
    label.tooltip = tip
    animation.update(rate)
  }
}

