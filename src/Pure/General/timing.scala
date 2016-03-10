/*  Title:      Pure/General/timing.scala
    Module:     PIDE
    Author:     Makarius

Basic support for time measurement.
*/

package isabelle


import java.util.Locale


object Timing
{
  val zero = Timing(Time.zero, Time.zero, Time.zero)

  def timeit[A](message: String, enabled: Boolean = true)(e: => A) =
    if (enabled) {
      val start = Time.now()
      val result = Exn.capture(e)
      val stop = Time.now()

      val timing = stop - start
      if (timing.is_relevant)
        Output.warning(
          (if (message == null || message.isEmpty) "" else message + ": ") +
            timing.message + " elapsed time")

      Exn.release(result)
    }
    else e
}

sealed case class Timing(elapsed: Time, cpu: Time, gc: Time)
{
  def is_relevant: Boolean = elapsed.is_relevant || cpu.is_relevant || gc.is_relevant

  def + (t: Timing): Timing = Timing(elapsed + t.elapsed, cpu + t.cpu, gc + t.gc)

  def message: String =
    elapsed.message + " elapsed time, " + cpu.message + " cpu time, " + gc.message + " GC time"

  def resources: Time = cpu + gc
  def message_resources: String =
  {
    val resources = cpu + gc
    val t1 = elapsed.seconds
    val t2 = resources.seconds
    val factor =
      if (t1 >= 3.0 && t2 >= 3.0)
        String.format(Locale.ROOT, ", factor %.2f", new java.lang.Double(t2 / t1))
      else ""
    if (t2 >= 3.0)
      elapsed.message_hms + " elapsed time, " + resources.message_hms + " cpu time" + factor
    else
      elapsed.message_hms + " elapsed time" + factor
  }

  override def toString: String = message
}
