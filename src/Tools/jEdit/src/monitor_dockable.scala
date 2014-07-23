/*  Title:      Tools/jEdit/src/monitor_dockable.scala
    Author:     Makarius

Monitor for runtime statistics.
*/

package isabelle.jedit


import isabelle._

import scala.swing.{TextArea, ScrollPane, Component}

import org.jfree.chart.ChartPanel
import org.jfree.data.xy.XYSeriesCollection

import org.gjt.sp.jedit.View


class Monitor_Dockable(view: View, position: String) extends Dockable(view, position)
{
  private val rev_stats = Synchronized(Nil: List[Properties.T])


  /* chart data -- owned by GUI thread */

  private val chart = ML_Statistics.empty.chart(null, Nil)
  private val data = chart.getXYPlot.getDataset.asInstanceOf[XYSeriesCollection]

  private val delay_update =
    GUI_Thread.delay_first(PIDE.options.seconds("editor_chart_delay")) {
      ML_Statistics("", rev_stats.value.reverse)
        .update_data(data, ML_Statistics.workers_fields._2) // FIXME selectable fields
    }

  set_content(new ChartPanel(chart))


  /* main */

  private val main =
    Session.Consumer[Session.Statistics](getClass.getName) {
      case stats =>
        rev_stats.change(stats.props :: _)
        delay_update.invoke()
    }

  override def init() { PIDE.session.statistics += main }
  override def exit() { PIDE.session.statistics -= main }
}

