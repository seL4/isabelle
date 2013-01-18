/*  Title:      Pure/ML/ml_statistics.ML
    Author:     Makarius

ML runtime statistics.
*/

package isabelle


import scala.collection.immutable.{SortedSet, SortedMap}
import scala.swing.{Frame, Component}

import org.jfree.data.xy.{XYSeries, XYSeriesCollection}
import org.jfree.chart.{JFreeChart, ChartPanel, ChartFactory}
import org.jfree.chart.plot.PlotOrientation


object ML_Statistics
{
  /* content interpretation */

  final case class Entry(time: Double, data: Map[String, Double])

  def apply(name: String, stats: List[Properties.T]): ML_Statistics =
    new ML_Statistics(name, stats)

  def apply(info: Build.Log_Info): ML_Statistics =
    apply(info.name, info.stats)

  val empty = apply("", Nil)


  /* standard fields */

  val GC_fields = ("GCs", List("partial_GCs", "full_GCs"))

  val heap_fields =
    ("Heap", List("size_heap", "size_allocation", "size_allocation_free",
      "size_heap_free_last_full_GC", "size_heap_free_last_GC"))

  val threads_fields =
    ("Threads", List("threads_total", "threads_in_ML", "threads_wait_condvar",
      "threads_wait_IO", "threads_wait_mutex", "threads_wait_signal"))

  val time_fields =
    ("Time", List("time_GC_system", "time_GC_user", "time_non_GC_system", "time_non_GC_user"))

  val tasks_fields =
    ("Future tasks",
      List("tasks_proof", "tasks_ready", "tasks_pending", "tasks_running", "tasks_passive"))

  val workers_fields =
    ("Worker threads", List("workers_total", "workers_active", "workers_waiting"))

  val standard_fields =
    List(GC_fields, heap_fields, threads_fields, time_fields, tasks_fields, workers_fields)
}

final class ML_Statistics private(val name: String, val stats: List[Properties.T])
{
  val Now = new Properties.Double("now")
  def now(props: Properties.T): Double = Now.unapply(props).get

  require(stats.forall(props => Now.unapply(props).isDefined))

  val time_start = if (stats.isEmpty) 0.0 else now(stats.head)
  val duration = if (stats.isEmpty) 0.0 else now(stats.last) - time_start

  val fields: Set[String] =
    SortedSet.empty[String] ++
      (for (props <- stats.iterator; (x, _) <- props.iterator if x != Now.name)
        yield x)

  val content: List[ML_Statistics.Entry] =
    stats.map(props => {
      val time = now(props) - time_start
      require(time >= 0.0)
      val data =
        SortedMap.empty[String, Double] ++
          (for ((x, y) <- props.iterator if x != Now.name)
            yield (x, java.lang.Double.parseDouble(y)))
      ML_Statistics.Entry(time, data)
    })


  /* charts */

  def update_data(data: XYSeriesCollection, selected_fields: Iterable[String])
  {
    data.removeAllSeries
    for {
      field <- selected_fields.iterator
      series = new XYSeries(field)
    } {
      content.foreach(entry => series.add(entry.time, entry.data(field)))
      data.addSeries(series)
    }
  }

  def chart(title: String, selected_fields: Iterable[String]): JFreeChart =
  {
    val data = new XYSeriesCollection
    update_data(data, selected_fields)

    ChartFactory.createXYLineChart(title, "time", "value", data,
      PlotOrientation.VERTICAL, true, true, true)
  }

  def chart(arg: (String, Iterable[String])): JFreeChart = chart(arg._1, arg._2)

  def show_standard_frames(): Unit =
    ML_Statistics.standard_fields.map(chart(_)).foreach(c =>
      Swing_Thread.later {
        new Frame {
          iconImage = Isabelle_System.get_icon().getImage
          title = name
          contents = Component.wrap(new ChartPanel(c))
          visible = true
        }
      })
}

