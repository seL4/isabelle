/*  Title:      Pure/Tools/build_stats.scala
    Author:     Makarius

Statistics from session build output.
*/

package isabelle


import scala.collection.mutable
import scala.util.matching.Regex


object Build_Stats
{
  private val Session_Finished =
    new Regex("""^Finished (\S+) \((\d+):(\d+):(\d+) elapsed time, (\d+):(\d+):(\d+) cpu time.*$""")
  private val Session_Timing =
    new Regex("""^Timing (\S+) \((\d) threads, (\d+\.\d+)s elapsed time, (\d+\.\d+)s cpu time, (\d+\.\d+)s GC time.*$""")

  private object ML_Option
  {
    def unapply(s: String): Option[(String, String)] =
      s.indexOf('=') match {
        case -1 => None
        case i =>
          val a = s.substring(0, i)
          Library.try_unquote(s.substring(i + 1)) match {
            case Some(b) if Build.ml_options.contains(a) => Some((a, b))
            case _ => None
          }
      }
  }

  def parse(text: String): Build_Stats =
  {
    import Properties.Value

    val ml_options = new mutable.ListBuffer[(String, String)]
    var finished = Map.empty[String, Timing]
    var timing = Map.empty[String, Timing]
    var threads = Map.empty[String, Int]

    for (line <- split_lines(text)) {
      line match {
        case Session_Finished(name,
            Value.Int(e1), Value.Int(e2), Value.Int(e3),
            Value.Int(c1), Value.Int(c2), Value.Int(c3)) =>
          val elapsed = Time.hours_minutes_seconds(e1, e2, e3)
          val cpu = Time.hours_minutes_seconds(c1, c2, c3)
          finished += (name -> Timing(elapsed, cpu, Time.zero))
        case Session_Timing(name,
            Value.Int(t), Value.Double(e), Value.Double(c), Value.Double(g)) =>
          val elapsed = Time.seconds(e)
          val cpu = Time.seconds(c)
          val gc = Time.seconds(g)
          timing += (name -> Timing(elapsed, cpu, gc))
          threads += (name -> t)
        case ML_Option(option) => ml_options += option
        case _ =>
      }
    }

    Build_Stats(ml_options.toList, finished, timing, threads)
  }
}

sealed case class Build_Stats(
  ml_options: List[(String, String)],
  finished: Map[String, Timing],
  timing: Map[String, Timing],
  threads: Map[String, Int])
{
  val sessions: Set[String] = finished.keySet ++ timing.keySet

  override def toString: String =
    sessions.toList.sorted.mkString("Build_Stats(", ", ", ")")
}
