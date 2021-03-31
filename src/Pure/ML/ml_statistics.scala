/*  Title:      Pure/ML/ml_statistics.scala
    Author:     Makarius

ML runtime statistics.
*/

package isabelle


import scala.annotation.tailrec
import scala.collection.mutable
import scala.collection.immutable.{SortedSet, SortedMap}
import scala.swing.{Frame, Component}

import org.jfree.data.xy.{XYSeries, XYSeriesCollection}
import org.jfree.chart.{JFreeChart, ChartPanel, ChartFactory}
import org.jfree.chart.plot.PlotOrientation


object ML_Statistics
{
  /* properties */

  val Now = new Properties.Double("now")
  def now(props: Properties.T): Double = Now.unapply(props).get


  /* memory status */

  val Heap_Size = new Properties.Long("size_heap")
  val Heap_Free = new Properties.Long("size_heap_free_last_GC")
  val GC_Percent = new Properties.Int("GC_percent")

  sealed case class Memory_Status(heap_size: Long, heap_free: Long, gc_percent: Int)
  {
    def heap_used: Long = (heap_size - heap_free) max 0
    def heap_used_fraction: Double =
      if (heap_size == 0) 0.0 else heap_used.toDouble / heap_size
    def gc_progress: Option[Double] =
      if (1 <= gc_percent && gc_percent <= 100) Some((gc_percent - 1) * 0.01) else None
  }

  def memory_status(props: Properties.T): Memory_Status =
  {
    val heap_size = Heap_Size.get(props)
    val heap_free = Heap_Free.get(props)
    val gc_percent = GC_Percent.get(props)
    Memory_Status(heap_size, heap_free, gc_percent)
  }


  /* monitor process */

  def monitor(pid: Long,
    stats_dir: String = "",
    delay: Time = Time.seconds(0.5),
    consume: Properties.T => Unit = Console.println): Unit =
  {
    def progress_stdout(line: String): Unit =
    {
      val props =
        Library.space_explode(',', line).flatMap((entry: String) =>
          Library.space_explode('=', entry) match {
            case List(a, b) => Some((a, b))
            case _ => None
          })
      if (props.nonEmpty) consume(props)
    }

    val env_prefix =
      if (stats_dir.isEmpty) "" else "export POLYSTATSDIR=" + Bash.string(stats_dir) + "\n"

    Bash.process(env_prefix + "exec \"$POLYML_EXE\" -q --use src/Pure/ML/ml_statistics.ML --eval " +
        Bash.string("ML_Statistics.monitor " + ML_Syntax.print_long(pid) + " " +
          ML_Syntax.print_double(delay.seconds)),
        cwd = Path.ISABELLE_HOME.file)
      .result(progress_stdout = progress_stdout, strict = false).check
  }


  /* protocol handler */

  class Handler extends Session.Protocol_Handler
  {
    private var session: Session = null
    private var monitoring: Future[Unit] = Future.value(())

    override def init(session: Session): Unit = synchronized
    {
      this.session = session
    }

    override def exit(): Unit = synchronized
    {
      session = null
      monitoring.cancel()
    }

    private def consume(props: Properties.T): Unit = synchronized
    {
      if (session != null) {
        val props1 = (session.cache.props(props ::: Java_Statistics.jvm_statistics()))
        session.runtime_statistics.post(Session.Runtime_Statistics(props1))
      }
    }

    private def ml_statistics(msg: Prover.Protocol_Output): Boolean = synchronized
    {
      msg.properties match {
        case Markup.ML_Statistics(pid, stats_dir) =>
          monitoring =
            Future.thread("ML_statistics") {
              monitor(pid, stats_dir = stats_dir, consume = consume)
            }
          true
        case _ => false
      }
    }

    override val functions = List(Markup.ML_Statistics.name -> ml_statistics)
  }


  /* memory fields (mega bytes) */

  def mem_print(x: Long): Option[String] =
    if (x == 0L) None else Some(x.toString + " M")

  def mem_scale(x: Long): Long = x / 1024 / 1024

  def mem_field_scale(name: String, x: Double): Double =
    if (heap_fields._2.contains(name) || program_fields._2.contains(name))
      mem_scale(x.toLong).toDouble
    else x

  val CODE_SIZE = "size_code"
  val STACK_SIZE = "size_stacks"
  val HEAP_SIZE = "size_heap"


  /* standard fields */

  type Fields = (String, List[String])

  val tasks_fields: Fields =
    ("Future tasks",
      List("tasks_ready", "tasks_pending", "tasks_running", "tasks_passive",
        "tasks_urgent", "tasks_total"))

  val workers_fields: Fields =
    ("Worker threads", List("workers_total", "workers_active", "workers_waiting"))

  val GC_fields: Fields =
    ("GCs", List("partial_GCs", "full_GCs", "share_passes"))

  val heap_fields: Fields =
    ("Heap", List(HEAP_SIZE, "size_allocation", "size_allocation_free",
      "size_heap_free_last_full_GC", "size_heap_free_last_GC"))

  val program_fields: Fields =
    ("Program", List("size_code", "size_stacks"))

  val threads_fields: Fields =
    ("Threads", List("threads_total", "threads_in_ML", "threads_wait_condvar",
      "threads_wait_IO", "threads_wait_mutex", "threads_wait_signal"))

  val time_fields: Fields =
    ("Time", List("time_elapsed", "time_elapsed_GC", "time_CPU", "time_GC"))

  val speed_fields: Fields =
    ("Speed", List("speed_CPU", "speed_GC"))

  private val time_speed = Map("time_CPU" -> "speed_CPU", "time_GC" -> "speed_GC")

  val java_heap_fields: Fields =
    ("Java heap", List("java_heap_size", "java_heap_used"))

  val java_thread_fields: Fields =
    ("Java threads", List("java_threads_total", "java_workers_total", "java_workers_active"))


  val main_fields: List[Fields] =
    List(heap_fields, tasks_fields, workers_fields)

  val other_fields: List[Fields] =
    List(threads_fields, GC_fields, program_fields, time_fields, speed_fields,
      java_heap_fields, java_thread_fields)

  val all_fields: List[Fields] = main_fields ::: other_fields


  /* content interpretation */

  final case class Entry(time: Double, data: Map[String, Double])
  {
    def get(field: String): Double = data.getOrElse(field, 0.0)
  }

  val empty: ML_Statistics = apply(Nil)

  def apply(ml_statistics0: List[Properties.T], heading: String = "",
    domain: String => Boolean = (key: String) => true): ML_Statistics =
  {
    require(ml_statistics0.forall(props => Now.unapply(props).isDefined), "missing \"now\" field")

    val ml_statistics = ml_statistics0.sortBy(now)
    val time_start = if (ml_statistics.isEmpty) 0.0 else now(ml_statistics.head)
    val duration = if (ml_statistics.isEmpty) 0.0 else now(ml_statistics.last) - time_start

    val fields =
      SortedSet.empty[String] ++
        (for {
          props <- ml_statistics.iterator
          (x, _) <- props.iterator
          if x != Now.name && domain(x) } yield x)

    val content =
    {
      var last_edge = Map.empty[String, (Double, Double, Double)]
      val result = new mutable.ListBuffer[ML_Statistics.Entry]
      for (props <- ml_statistics) {
        val time = now(props) - time_start

        // rising edges -- relative speed
        val speeds =
          (for {
            (key, value) <- props.iterator
            key1 <- time_speed.get(key)
            if domain(key1)
          } yield {
            val (x0, y0, s0) = last_edge.getOrElse(key, (0.0, 0.0, 0.0))

            val x1 = time
            val y1 = java.lang.Double.parseDouble(value)
            val s1 = if (x1 == x0) 0.0 else (y1 - y0) / (x1 - x0)

            if (y1 > y0) {
              last_edge += (key -> (x1, y1, s1))
              (key1, s1.toString)
            }
            else (key1, s0.toString)
          }).toList

        val data =
          SortedMap.empty[String, Double] ++
            (for {
              (x, y) <- props.iterator ++ speeds.iterator
              if x != Now.name && domain(x)
              z = java.lang.Double.parseDouble(y) if z != 0.0
            } yield { (x.intern, mem_field_scale(x, z)) })

        result += ML_Statistics.Entry(time, data)
      }
      result.toList
    }

    new ML_Statistics(heading, fields, content, time_start, duration)
  }
}

final class ML_Statistics private(
  val heading: String,
  val fields: Set[String],
  val content: List[ML_Statistics.Entry],
  val time_start: Double,
  val duration: Double)
{
  /* content */

  def maximum(field: String): Double =
    content.foldLeft(0.0) { case (m, e) => m max e.get(field) }

  def average(field: String): Double =
  {
    @tailrec def sum(t0: Double, list: List[ML_Statistics.Entry], acc: Double): Double =
      list match {
        case Nil => acc
        case e :: es =>
          val t = e.time
          sum(t, es, (t - t0) * e.get(field) + acc)
      }
    content match {
      case Nil => 0.0
      case List(e) => e.get(field)
      case e :: es => sum(e.time, es, 0.0) / duration
    }
  }


  /* charts */

  def update_data(data: XYSeriesCollection, selected_fields: List[String]): Unit =
  {
    data.removeAllSeries
    for (field <- selected_fields) {
      val series = new XYSeries(field)
      content.foreach(entry => series.add(entry.time, entry.get(field)))
      data.addSeries(series)
    }
  }

  def chart(title: String, selected_fields: List[String]): JFreeChart =
  {
    val data = new XYSeriesCollection
    update_data(data, selected_fields)

    ChartFactory.createXYLineChart(title, "time", "value", data,
      PlotOrientation.VERTICAL, true, true, true)
  }

  def chart(fields: ML_Statistics.Fields): JFreeChart =
    chart(fields._1, fields._2)

  def show_frames(fields: List[ML_Statistics.Fields] = ML_Statistics.main_fields): Unit =
    fields.map(chart).foreach(c =>
      GUI_Thread.later {
        new Frame {
          iconImage = GUI.isabelle_image()
          title = heading
          contents = Component.wrap(new ChartPanel(c))
          visible = true
        }
      })
}
