/*  Title:      Pure/General/timing.scala
    Author:     Makarius

Basic support for time measurement.
*/

package isabelle


sealed case class Timing(val elapsed: Double, cpu: Double, gc: Double)
{
  private def print_time(seconds: Double): String =
    String.format(java.util.Locale.ROOT, "%.3f", seconds.asInstanceOf[AnyRef])

  def message: String =
    print_time(elapsed) + "s elapsed time, " +
    print_time(cpu) + "s cpu time, " +
    print_time(gc) + "s GC time"
}

