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
import org.jfree.chart.renderer.xy.XYLineAndShapeRenderer
import org.jfree.chart.{JFreeChart, ChartPanel, ChartFactory}
import org.jfree.chart.plot.{PlotOrientation, XYPlot}
import org.jfree.data.xy.XYDataset


object ML_Statistics {
  /* properties */

  def parse_properties(s: String): Properties.T =
    space_explode(',', s).flatMap(Properties.Eq.unapply)

  val GC_Percent = new Properties.Int("GC_percent")


  /* fields */

  class Field(name: String, description: String = "") extends Properties.Double_View(name) {
    def domain: Set[String] = Set(name)
    def title: String = proper_string(description).getOrElse(Word.informal(name))
    def get_space(props: Properties.T): Space = Space.B(get(props))
    def get_time(props: Properties.T): Time = Time.seconds(get(props))
    def scale(y: Double): Double = y
  }

  class Field_MiB(name: String, description: String = "") extends Field(name, description = description) {
    override def scale(y: Double): Double = Space.B(y).MiB
  }

  val Now = new Field("now")
  def now(props: Properties.T): Double = Now.unapply(props).get

  val Heap_Size = new Field_MiB("size_heap", description =  "heap size")
  val Heap_Free_Minor = new Field_MiB("size_heap_free_last_GC", description = "heap free (minor GC)")
  val Heap_Free_Major = new Field_MiB("size_heap_free_last_full_GC", description = "heap free (major GC)")
  val Heap_Size_Allocation = new Field_MiB("size_allocation", description = "heap size (allocation)")
  val Heap_Free_Allocation = new Field_MiB("size_allocation_free", description = "heap free (allocation)")

  val Tasks_Ready = new Field("tasks_ready")
  val Tasks_Pending = new Field("tasks_pending")
  val Tasks_Running = new Field("tasks_running")
  val Tasks_Passive = new Field("tasks_passive")
  val Tasks_Urgent = new Field("tasks_urgent")
  val Tasks_Total = new Field("tasks_total")

  val Workers_Total = new Field("workers_total")
  val Workers_Active = new Field("workers_active")
  val Workers_Waiting = new Field("workers_waiting")

  val GCs_Minor = new Field("partial_GCs", description = "GCs (minor)")
  val GCs_Major = new Field("full_GCs", description = "GCs (major)")
  val GCs_Sharing = new Field("share_passes", description = "GCs (sharing)")

  val Program_Code = new Field_MiB("size_code", description = "program code)")
  val Program_Stack = new Field_MiB("size_stacks", description = "program stack")

  val Threads_Total = new Field("threads_total")
  val Threads_ML = new Field("threads_in_ML", description = "threads (ML)")
  val Threads_Wait_Condvar = new Field("threads_wait_condvar")
  val Threads_Wait_IO = new Field("threads_wait_IO")
  val Threads_Wait_Mutex = new Field("threads_wait_mutex")
  val Threads_Wait_Signal = new Field("threads_wait_signal")

  val Time_Elapsed = new Field("time_elapsed")
  val Time_Elapsed_GC = new Field("time_elapsed_GC")
  val Time_CPU = new Field("time_CPU")
  val Time_GC = new Field("time_GC")

  val Speed_CPU = new Field("speed_CPU")
  val Speed_GC = new Field("speed_GC")

  val Java_Heap_Size = new Field_MiB("java_heap_size", description = "Java heap size")
  val Java_Heap_Used = new Field_MiB("java_heap_used", description = "Java heap used")
  val Java_Heap_Free: Field_MiB =
    new Field_MiB("java_heap_free", description = "Java heap free") {
      override def domain: Set[String] = Set(name, Java_Heap_Used.name)
      override def unapply(props: Properties.T): Option[Double] =
        for {
          size <- Java_Heap_Size.unapply(props)
          used <- Java_Heap_Used.unapply(props)
        } yield size - used
    }
  val Java_Heap_Size_Major = new Field_MiB("java_heap_size_major", description = "Java heap size (major GC)")
  val Java_Heap_Used_Major = new Field_MiB("java_heap_used_major", description = "Java heap used (major GC)")
  val Java_Heap_Free_Major: Field_MiB =
    new Field_MiB("java_heap_free_major", description = "Java heap free (major GC)") {
      override def domain: Set[String] = Set(name, Java_Heap_Used_Major.name)
      override def unapply(props: Properties.T): Option[Double] =
        for {
          size <- Java_Heap_Size_Major.unapply(props)
          used <- Java_Heap_Used_Major.unapply(props)
        } yield size - used
    }
  val Java_Threads_Total = new Field("java_threads_total", description = "Java threads total")
  val Java_Workers_Total = new Field("java_workers_total", description = "Java workers total")
  val Java_Workers_Active = new Field("java_workers_active", description = "Java workers active")


  /* memory status */

  sealed case class Memory_Status(
    heap_size: Space,
    heap_free_minor: Space,
    heap_free_major: Space,
    gc_percent: Int
  ) {
    def heap_used_minor: Space = heap_size.used(heap_free_minor)
    def heap_used_minor_fraction: Double = heap_size.used_fraction(heap_free_minor)
    def heap_used_major: Space = heap_size.used(heap_free_major)
    def heap_used_major_fraction: Double = heap_size.used_fraction(heap_free_major)
    def gc_progress: Option[Double] =
      if (1 <= gc_percent && gc_percent <= 100) Some((gc_percent - 1) * 0.01) else None
  }

  def memory_status(props: Properties.T): Memory_Status = {
    val heap_size = Heap_Size.get_space(props)
    val heap_free_minor = Heap_Free_Minor.get_space(props)
    val heap_free_major = Heap_Free_Major.get_space(props)
    val gc_percent = GC_Percent.get(props)
    Memory_Status(heap_size, heap_free_minor, heap_free_major, gc_percent)
  }


  /* monitor process */

  def monitor(ml_settings: ML_Settings, pid: Long,
    stats_dir: String = "",
    delay: Time = Time.seconds(0.5),
    consume: Properties.T => Unit = Console.println
  ): Unit = {
    def progress_stdout(line: String): Unit = {
      val props = parse_properties(line)
      if (props.nonEmpty) consume(props)
    }

    val env_prefix = if_proper(stats_dir, Bash.exports("POLYSTATSDIR=" + stats_dir))

    Bash.process(env_prefix + File.bash_path(ml_settings.polyml_exe) +
        " -q --use src/Pure/ML/ml_statistics.ML --eval " +
        Bash.string("ML_Statistics.monitor " + ML_Syntax.print_long(pid) + " " +
          ML_Syntax.print_double(delay.seconds)),
        cwd = Path.ISABELLE_HOME)
      .result(progress_stdout = progress_stdout, strict = false).check
  }


  /* protocol handler */

  class Handler extends Session.Protocol_Handler {
    private var session: Session = null
    private var monitoring: Future[Unit] = Future.value(())

    override def init(session: Session): Unit = synchronized {
      this.session = session
    }

    override def exit(exit_state: Document.State): Unit = synchronized {
      session = null
      monitoring.cancel()
    }

    private def consume(props: Properties.T): Unit = synchronized {
      if (session != null) {
        val props1 = session.cache.props(props ::: Java_Statistics.jvm_statistics())
        session.runtime_statistics.post(Session.Runtime_Statistics(props1))
      }
    }

    private def ml_statistics(msg: Prover.Protocol_Output): Boolean = synchronized {
      msg.properties match {
        case Markup.ML_Statistics(pid, stats_dir) =>
          monitoring =
            Future.thread("ML_statistics") {
              monitor(session.store.ml_settings, pid, stats_dir = stats_dir, consume = consume)
            }
          true
        case _ => false
      }
    }

    override val functions: Session.Protocol_Functions =
      List(Markup.ML_Statistics.name -> ml_statistics)
  }


  /* standard fields */

  sealed case class Fields(title: String, content: List[Field])

  val tasks_fields: Fields =
    Fields("Future tasks",
      List(Tasks_Ready, Tasks_Pending, Tasks_Running, Tasks_Passive,
        Tasks_Urgent, Tasks_Total))

  val workers_fields: Fields =
    Fields("Worker threads", List(Workers_Total, Workers_Active, Workers_Waiting))

  val GCs_fields: Fields =
    Fields("GCs", List(GCs_Minor, GCs_Major, GCs_Sharing))

  val heap_fields: Fields =
    Fields("Heap", List(Heap_Size, Heap_Size_Allocation, Heap_Free_Allocation,
      Heap_Free_Major, Heap_Free_Minor))

  val program_fields: Fields =
    Fields("Program", List(Program_Code, Program_Stack))

  val threads_fields: Fields =
    Fields("Threads", List(Threads_Total, Threads_ML, Threads_Wait_Condvar,
      Threads_Wait_IO, Threads_Wait_Mutex, Threads_Wait_Signal))

  val time_fields: Fields =
    Fields("Time", List(Time_Elapsed, Time_Elapsed_GC, Time_CPU, Time_GC))

  val speed_fields: Fields =
    Fields("Speed", List(Speed_CPU, Speed_GC))

  private val time_speed =
    Map(Time_CPU.name -> Speed_CPU.name, Time_GC.name -> Speed_GC.name)

  val java_heap_fields: Fields =
    Fields("Java heap", List(Java_Heap_Size, Java_Heap_Free,
      Java_Heap_Size_Major, Java_Heap_Free_Major))

  val java_thread_fields: Fields =
    Fields("Java threads", List(Java_Threads_Total, Java_Workers_Total, Java_Workers_Active))


  val main_fields: List[Fields] =
    List(heap_fields, tasks_fields, workers_fields)

  val other_fields: List[Fields] =
    List(threads_fields, GCs_fields, program_fields, time_fields, speed_fields,
      java_heap_fields, java_thread_fields)

  val all_fields: List[Fields] = main_fields ::: other_fields


  /* content interpretation */

  final case class Entry(time: Double, data: Map[String, Double]) {
    def get(field: Field): Double = field.scale(data.getOrElse(field.name, 0.0))
  }

  val empty: ML_Statistics = apply(Nil)

  def apply(
    ml_statistics0: List[Properties.T],
    heading: String = "",
    domain: String => Boolean = _ => true
  ): ML_Statistics = {
    require(ml_statistics0.forall(props => Now.unapply(props).isDefined), "missing \"now\" field")

    val ml_statistics = ml_statistics0.sortBy(now)
    val time_start = if (ml_statistics.isEmpty) 0.0 else now(ml_statistics.head)
    val time_stop = if (ml_statistics.isEmpty) 0.0 else now(ml_statistics.last)

    val fields =
      SortedSet.from[String](
        for {
          props <- ml_statistics.iterator
          (x, _) <- props.iterator
          if x != Now.name && domain(x) } yield x)

    val content = {
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
          SortedMap.from[String, Double](
            for {
              (x, y) <- props.iterator ++ speeds.iterator
              if x != Now.name && domain(x)
              z = java.lang.Double.parseDouble(y) if z != 0.0
            } yield { (x.intern, z) })

        result += ML_Statistics.Entry(time, data)
      }
      result.toList
    }

    new ML_Statistics(heading, fields, content, time_start, time_stop)
  }

  def make_domain(fields: List[Field]): Set[String] =
    Set.from(
      for {
        field <- fields.iterator
        name <- field.domain.iterator
      } yield name)
}

final class ML_Statistics private(
  val heading: String,
  val fields: Set[String],
  val content: List[ML_Statistics.Entry],
  val time_start: Double,
  val time_stop: Double
) {
  override def toString: String =
    if (content.isEmpty) "ML_Statistics.empty"
    else "ML_Statistics(length = " + content.length + ", fields = " + fields.size + ")"

  def duration: Double = time_stop - time_start


  /* content */

  def maximum(field: ML_Statistics.Field): Double =
    content.foldLeft(0.0) { case (m, e) => m max e.get(field) }

  def average(field: ML_Statistics.Field): Double = {
    @tailrec def sum(t0: Double, list: List[ML_Statistics.Entry], acc: Double): Double =
      list match {
        case Nil => acc
        case e :: es =>
          val t = e.time
          sum(t, es, (t - t0) * e.get(field) + acc)
      }
    content match {
      case e :: es if duration > 0 => sum(e.time, es, 0.0) / duration
      case List(e) => e.get(field)
      case _ => 0.0
    }
  }


  /* memory content */

  def maximum_code: Space = Space.B(maximum(ML_Statistics.Program_Code))
  def average_code: Space = Space.B(average(ML_Statistics.Program_Code))
  def maximum_stack: Space = Space.B(maximum(ML_Statistics.Program_Stack))
  def average_stack: Space = Space.B(average(ML_Statistics.Program_Stack))
  def maximum_heap: Space = Space.B(maximum(ML_Statistics.Heap_Size))
  def average_heap: Space = Space.B(average(ML_Statistics.Heap_Size))

  def maximum_java_heap: Space = Space.B(maximum(ML_Statistics.Java_Heap_Size))
  def average_java_heap: Space = Space.B(average(ML_Statistics.Java_Heap_Size))
  def maximum_java_heap_major: Space = Space.B(maximum(ML_Statistics.Java_Heap_Size_Major))
  def average_java_heap_major: Space = Space.B(average(ML_Statistics.Java_Heap_Size_Major))


  /* charts */

  def update_data(data: XYSeriesCollection, selected_fields: List[ML_Statistics.Field]): Unit = {
    data.removeAllSeries()
    for (field <- selected_fields) {
      val series = new XYSeries(field.name)
      series.setDescription(field.title)
      content.foreach(e => series.add(e.time, e.get(field)))
      data.addSeries(series)
    }
  }

  def chart(title: String, selected_fields: List[ML_Statistics.Field]): JFreeChart = {
    val data = new XYSeriesCollection
    update_data(data, selected_fields)

    val chart =
      ChartFactory.createXYLineChart(title, "time", "value", data,
        PlotOrientation.VERTICAL, true, true, true)

    chart.getPlot.asInstanceOf[XYPlot].getRenderer.asInstanceOf[XYLineAndShapeRenderer]
      .setLegendItemLabelGenerator((dataset: XYDataset, series: Int) =>
        dataset match {
          case datas: XYSeriesCollection => datas.getSeries(series).getDescription
          case _ => "undefined"
        })

    chart
  }

  def chart(fields: ML_Statistics.Fields): JFreeChart =
    chart(fields.title, fields.content)

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
