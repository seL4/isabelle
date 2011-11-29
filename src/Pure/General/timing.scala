/*  Title:      Pure/General/timing.scala
    Author:     Makarius

Basic support for time measurement.
*/

package isabelle


object Timing
{
  def timeit[A](message: String)(e: => A) =
  {
    val start = java.lang.System.currentTimeMillis()
    val result = Exn.capture(e)
    val stop = java.lang.System.currentTimeMillis()
    java.lang.System.err.println(
      (if (message == null || message.isEmpty) "" else message + ": ") +
        Time.ms(stop - start).message + " elapsed time")
    Exn.release(result)
  }
}

class Timing(val elapsed: Time, val cpu: Time, val gc: Time)
{
  def message: String =
    elapsed.message + " elapsed time, " + cpu.message + " cpu time, " + gc.message + " GC time"
  override def toString = message
}

