/*  Title:      Tools/jEdit/src/monitor_dockable.scala
    Author:     Makarius

Monitor for runtime statistics.
*/

package isabelle.jedit


import isabelle._

import scala.actors.Actor._
import scala.swing.{TextArea, ScrollPane, Component}

import org.jfree.chart.{ChartFactory, ChartPanel}
import org.jfree.data.time.{Millisecond, TimeSeries, TimeSeriesCollection}

import org.gjt.sp.jedit.View


class Monitor_Dockable(view: View, position: String) extends Dockable(view, position)
{
  /* properties */  // FIXME avoid hardwired stuff

  private val Now = new Properties.Double("now")
  private val Size_Heap = new Properties.Double("size_heap")

  private val series = new TimeSeries("ML heap size", classOf[Millisecond])


  /* chart */

  private val chart_panel =
  {
    val data = new TimeSeriesCollection(series)
    val chart = ChartFactory.createTimeSeriesChart(null, "Time", "Value", data, true, true, false)
    val plot = chart.getXYPlot()

    val x_axis = plot.getDomainAxis()
    x_axis.setAutoRange(true)
    x_axis.setFixedAutoRange(60000.0)

    val y_axis = plot.getRangeAxis()
    y_axis.setAutoRange(true)

    new ChartPanel(chart)
  }
  set_content(chart_panel)


  /* main actor */

  private val main_actor = actor {
    var t0: Option[Double] = None
    loop {
      react {
        case Session.Statistics(stats) =>
          java.lang.System.err.println(stats)
          stats match {
            case Now(t1) =>
              if (t0.isEmpty) t0 = Some(t1)
              val t = t1 - t0.get
              stats match {
                case Size_Heap(x) => series.add(new Millisecond(), x)  // FIXME proper time point
                case _ =>
              }
            case _ =>
          }
        case bad => java.lang.System.err.println("Monitor_Dockable: ignoring bad message " + bad)
      }
    }
  }

  override def init() { PIDE.session.statistics += main_actor }
  override def exit() { PIDE.session.statistics -= main_actor }
}

