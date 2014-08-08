/*  Title:      Tools/jEdit/src/monitor_dockable.scala
    Author:     Makarius

Monitor for ML statistics.
*/

package isabelle.jedit


import isabelle._

import java.awt.BorderLayout

import scala.swing.{TextArea, ScrollPane, Component, ComboBox, Button}
import scala.swing.event.{SelectionChanged, ButtonClicked}

import org.jfree.chart.ChartPanel
import org.jfree.data.xy.XYSeriesCollection

import org.gjt.sp.jedit.View


class Monitor_Dockable(view: View, position: String) extends Dockable(view, position)
{
  private val rev_stats = Synchronized(Nil: List[Properties.T])


  /* chart data -- owned by GUI thread */

  private var data_name = ML_Statistics.standard_fields(0)._1
  private val chart = ML_Statistics.empty.chart(null, Nil)
  private val data = chart.getXYPlot.getDataset.asInstanceOf[XYSeriesCollection]

  private def update_chart: Unit =
    ML_Statistics.standard_fields.find(_._1 == data_name) match {
      case None =>
      case Some((_, fields)) =>
        ML_Statistics("", rev_stats.value.reverse).update_data(data, fields)
    }

  private val delay_update =
    GUI_Thread.delay_first(PIDE.options.seconds("editor_chart_delay")) { update_chart }


  /* controls */

  private val select_data = new ComboBox[String](
    ML_Statistics.standard_fields.map(_._1))
  {
    tooltip = "Select visualized data collection"
    listenTo(selection)
    reactions += {
      case SelectionChanged(_) =>
        data_name = selection.item
        update_chart
    }
  }

  val reset_data = new Button("Reset") {
    tooltip = "Reset accumulated data"
    reactions += {
      case ButtonClicked(_) =>
        rev_stats.change(_ => Nil)
        update_chart
    }
  }

  private val controls = new Wrap_Panel(Wrap_Panel.Alignment.Right)(select_data, reset_data)


  /* layout */

  set_content(new ChartPanel(chart))
  add(controls.peer, BorderLayout.NORTH)


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

