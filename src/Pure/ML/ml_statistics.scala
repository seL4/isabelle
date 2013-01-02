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

  def apply(stats: List[Properties.T]): ML_Statistics = new ML_Statistics(stats)
  def apply(log: Path): ML_Statistics = apply(read_log(log))


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
    ("Future tasks", List("tasks_ready", "tasks_pending", "tasks_running", "tasks_passive"))

  val workers_fields =
    ("Worker threads", List("workers_total", "workers_active", "workers_waiting"))

  val standard_fields =
    List(GC_fields, heap_fields, threads_fields, time_fields, tasks_fields, workers_fields)


  /* read properties from build log */

  private val line_prefix = "\fML_statistics = "

  private val syntax = Outer_Syntax.empty + "," + "(" + ")" + "[" + "]"

  private object Parser extends Parse.Parser
  {
    private def stat: Parser[(String, String)] =
      keyword("(") ~ string ~ keyword(",") ~ string ~ keyword(")") ^^
      { case _ ~ x ~ _ ~ y ~ _ => (x, y) }
    private def stats: Parser[Properties.T] =
      keyword("[") ~> repsep(stat, keyword(",")) <~ keyword("]")

    def parse_stats(s: String): Properties.T =
    {
      parse_all(stats, Token.reader(syntax.scan(s))) match {
        case Success(result, _) => result
        case bad => error(bad.toString)
      }
    }
  }

  def read_log(log: Path): List[Properties.T] =
    for {
      line <- split_lines(File.read_gzip(log))
      if line.startsWith(line_prefix)
      stats = line.substring(line_prefix.length)
    } yield Parser.parse_stats(stats)
}

final class ML_Statistics private(val stats: List[Properties.T])
{
  val Now = new Properties.Double("now")

  require(!stats.isEmpty && stats.forall(props => Now.unapply(props).isDefined))

  val time_start = Now.unapply(stats.head).get
  val duration = Now.unapply(stats.last).get - time_start

  val fields: Set[String] =
    SortedSet.empty[String] ++
      (for (props <- stats.iterator; (x, _) <- props.iterator if x != Now.name)
        yield x)

  val content: List[ML_Statistics.Entry] =
    stats.map(props => {
      val time = Now.unapply(props).get - time_start
      require(time >= 0.0)
      val data =
        SortedMap.empty[String, Double] ++
          (for ((x, y) <- props.iterator if x != Now.name)
            yield (x, java.lang.Double.parseDouble(y)))
      ML_Statistics.Entry(time, data)
    })


  /* charts */

  def chart(title: String, selected_fields: Iterable[String]): JFreeChart =
  {
    val data = new XYSeriesCollection

    for {
      field <- selected_fields.iterator
      series = new XYSeries(field)
    } {
      content.foreach(entry => series.add(entry.time, entry.data(field)))
      data.addSeries(series)
    }

    ChartFactory.createXYLineChart(title, "time", "value", data,
      PlotOrientation.VERTICAL, true, true, true)
  }

  def chart_panel(title: String, selected_fields: Iterable[String]): ChartPanel =
    new ChartPanel(chart(title, selected_fields))

  def standard_frames: Unit =
    for ((title, selected_fields) <- ML_Statistics.standard_fields) {
      val c = chart(title, selected_fields)
      Swing_Thread.later {
        new Frame { contents = Component.wrap(new ChartPanel(c)); visible = true }
      }
    }
}

