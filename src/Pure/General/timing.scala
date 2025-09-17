/*  Title:      Pure/General/timing.scala
    Author:     Makarius

Support for time measurement.
*/

package isabelle


import java.util.Locale


object Timing {
  val zero: Timing = Timing(Time.zero, Time.zero, Time.zero)

  def timeit[A](body: => A,
    message: Exn.Result[A] => String = null,
    enabled: Boolean = true,
    output: String => Unit = Output.warning(_)
  ): A = {
    if (enabled) {
      val start = Time.now()
      val result = Exn.capture(body)
      val stop = Time.now()

      val timing = stop - start
      if (timing.is_relevant) {
        val msg = if (message == null) null else message(result)
        output(if_proper(msg, msg + ": ") + timing.message + " elapsed time")
      }

      Exn.release(result)
    }
    else body
  }

  def factor_format(f: Double): String =
    String.format(Locale.ROOT, ", factor %.2f", java.lang.Double.valueOf(f))

  def merge(args: IterableOnce[Timing]): Timing =
    args.iterator.foldLeft(zero)(_ + _)
}

sealed case class Timing(elapsed: Time, cpu: Time, gc: Time) {
  def is_zero: Boolean = elapsed.is_zero && cpu.is_zero && gc.is_zero
  def is_relevant: Boolean = elapsed.is_relevant || cpu.is_relevant || gc.is_relevant
  def is_notable(threshold: Time): Boolean = is_relevant && elapsed.is_notable(threshold)

  def resources: Time = cpu + gc

  def factor: Option[Double] = {
    val t1 = elapsed.seconds
    val t2 = resources.seconds
    if (t1 >= 3.0 && t2 >= 3.0) Some(t2 / t1) else None
  }

  def + (t: Timing): Timing = Timing(elapsed + t.elapsed, cpu + t.cpu, gc + t.gc)

  def message: String =
    elapsed.message + " elapsed time, " + cpu.message + " cpu time, " + gc.message + " GC time"

  def message_factor: String =
    elapsed.message + " elapsed time, " + cpu.message + " cpu time, " + gc.message + " GC time" +
      Timing.factor_format(cpu.seconds / elapsed.seconds)

  def message_resources: String = {
    val factor_text =
      factor match {
        case Some(f) => Timing.factor_format(f)
        case None => ""
      }
    if (resources.seconds >= 3.0) {
      elapsed.message_hms + " elapsed time, " + resources.message_hms + " cpu time" + factor_text
    }
    else {
      elapsed.message_hms + " elapsed time" + factor_text
    }
  }

  override def toString: String = message

  def json: JSON.Object.T =
    JSON.Object("elapsed" -> elapsed.seconds, "cpu" -> cpu.seconds, "gc" -> gc.seconds)
}
