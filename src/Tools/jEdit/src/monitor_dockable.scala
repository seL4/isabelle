/*  Title:      Tools/jEdit/src/monitor_dockable.scala
    Author:     Makarius

Monitor for ML statistics.
*/

package isabelle.jedit


import isabelle._

import java.awt.BorderLayout

import scala.collection.immutable.Queue
import scala.swing.{TextArea, TextField, ScrollPane, Component, ComboBox, Button}
import scala.swing.event.{SelectionChanged, ButtonClicked, ValueChanged}

import org.jfree.chart.ChartPanel
import org.jfree.data.xy.XYSeriesCollection

import org.gjt.sp.jedit.View


class Monitor_Dockable(view: View, position: String) extends Dockable(view, position)
{
  /* chart data -- owned by GUI thread */

  private var statistics = Queue.empty[Properties.T]
  private var statistics_length = 0

  private def add_statistics(stats: Properties.T)
  {
    statistics = statistics.enqueue(stats)
    statistics_length += 1
    limit_data.text match {
      case Value.Int(limit) =>
        while (statistics_length > limit) {
          statistics = statistics.dequeue._2
          statistics_length -= 1
        }
      case _ =>
    }
  }
  private def clear_statistics()
  {
    statistics = Queue.empty
    statistics_length = 0
  }

  private var data_name = ML_Statistics.all_fields(0)._1
  private val chart = ML_Statistics.empty.chart(null, Nil)
  private val data = chart.getXYPlot.getDataset.asInstanceOf[XYSeriesCollection]

  private def update_chart: Unit =
    ML_Statistics.all_fields.find(_._1 == data_name) match {
      case None =>
      case Some((_, fields)) => ML_Statistics(statistics.toList).update_data(data, fields)
    }

  private val input_delay =
    GUI_Thread.delay_first(PIDE.options.seconds("editor_input_delay")) { update_chart }

  private val update_delay =
    GUI_Thread.delay_first(PIDE.options.seconds("editor_chart_delay")) { update_chart }


  /* controls */

  private val ml_stats = new Isabelle.ML_Stats

  private val select_data = new ComboBox[String](ML_Statistics.all_fields.map(_._1))
  {
    tooltip = "Select visualized data collection"
    listenTo(selection)
    reactions += {
      case SelectionChanged(_) =>
        data_name = selection.item
        update_chart
    }
  }

  private val reset_data = new Button("Reset") {
    tooltip = "Reset accumulated data"
    reactions += {
      case ButtonClicked(_) => clear_statistics()
        update_chart
    }
  }

  private val limit_data = new TextField("200", 5) {
    tooltip = "Limit for accumulated data"
    verifier = (s: String) =>
      s match { case Value.Int(x) => x > 0 case _ => false }
    reactions += { case ValueChanged(_) => input_delay.invoke() }
  }

  private val controls =
    Wrap_Panel(List(ml_stats, select_data, reset_data, limit_data),
      Wrap_Panel.Alignment.Right)


  /* layout */

  set_content(new ChartPanel(chart))
  add(controls.peer, BorderLayout.NORTH)


  /* main */

  private val main =
    Session.Consumer[Any](getClass.getName) {
      case stats: Session.Statistics =>
        add_statistics(stats.props)
        update_delay.invoke()

      case _: Session.Global_Options =>
        GUI_Thread.later { ml_stats.load() }
    }

  override def init()
  {
    PIDE.session.statistics += main
    PIDE.session.global_options += main
  }

  override def exit()
  {
    PIDE.session.statistics -= main
    PIDE.session.global_options -= main
  }
}
