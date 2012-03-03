/*  Title:      Pure/General/time.scala
    Module:     PIDE
    Author:     Makarius

Time based on milliseconds.
*/

package isabelle


object Time
{
  def seconds(s: Double): Time = new Time((s * 1000.0) round)
  def ms(m: Long): Time = new Time(m)
}

final class Time private(val ms: Long)
{
  def seconds: Double = ms / 1000.0

  def min(t: Time): Time = if (ms < t.ms) this else t
  def max(t: Time): Time = if (ms > t.ms) this else t

  def is_relevant: Boolean = ms >= 1

  override def toString =
    String.format(java.util.Locale.ROOT, "%.3f", seconds.asInstanceOf[AnyRef])

  def message: String = toString + "s"
}

