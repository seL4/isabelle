/*  Title:      Tools/jEdit/src/monitor_dockable.scala
    Author:     Makarius

Monitor for runtime statistics.
*/

package isabelle.jedit


import isabelle._

import scala.actors.Actor._
import scala.swing.{TextArea, ScrollPane, Component}

import org.jfree.chart.ChartPanel
import org.jfree.data.xy.XYSeriesCollection

import org.gjt.sp.jedit.View


class Monitor_Dockable(view: View, position: String) extends Dockable(view, position)
{
  /* chart data -- owned by Swing thread */

  private val chart = ML_Statistics.empty.chart(null, Nil)
  private val data = chart.getXYPlot.getDataset.asInstanceOf[XYSeriesCollection]
  private var rev_stats: List[Properties.T] = Nil

  private val delay_update =
    Swing_Thread.delay_first(PIDE.options.seconds("editor_chart_delay")) {
      ML_Statistics("", rev_stats.reverse)
        .update_data(data, ML_Statistics.workers_fields._2) // FIXME selectable fields
    }

  set_content(new ChartPanel(chart))


  /* main actor */

  private val main_actor = actor {
    loop {
      react {
        case Session.Statistics(props) =>
          Swing_Thread.later {
            rev_stats ::= props
            delay_update.invoke()
          }

        case bad => System.err.println("Monitor_Dockable: ignoring bad message " + bad)
      }
    }
  }

  override def init() { PIDE.session.statistics += main_actor }
  override def exit() { PIDE.session.statistics -= main_actor }
}

