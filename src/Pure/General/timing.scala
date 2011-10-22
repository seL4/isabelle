/*  Title:      Pure/General/timing.scala
    Author:     Makarius

Basic support for time measurement.
*/

package isabelle

object Time
{
  def seconds(s: Double): Time = new Time((s * 1000.0) round)
  def ms(m: Long): Time = new Time(m)
}

class Time private(val ms: Long)
{
  def seconds: Double = ms / 1000.0

  def min(t: Time): Time = if (ms < t.ms) this else t
  def max(t: Time): Time = if (ms > t.ms) this else t

  override def toString =
    String.format(java.util.Locale.ROOT, "%.3f", seconds.asInstanceOf[AnyRef])
  def message: String = toString + "s"
}

class Timing(val elapsed: Time, val cpu: Time, val gc: Time)
{
  def message: String =
    elapsed.message + " elapsed time, " + cpu.message + " cpu time, " + gc.message + " GC time"
  override def toString = message
}

