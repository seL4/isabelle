/*  Title:      Pure/General/time.scala
    Module:     PIDE
    Author:     Makarius

Time based on milliseconds.
*/

package isabelle


import java.util.Locale


object Time
{
  def seconds(s: Double): Time = new Time((s * 1000.0).round)
  def ms(m: Long): Time = new Time(m)
  val zero: Time = ms(0)

  def print_seconds(s: Double): String =
    String.format(Locale.ROOT, "%.3f", s.asInstanceOf[AnyRef])
}

final class Time private(val ms: Long) extends AnyVal
{
  def + (t: Time): Time = new Time(ms + t.ms)

  def seconds: Double = ms / 1000.0

  def min(t: Time): Time = if (ms < t.ms) this else t
  def max(t: Time): Time = if (ms > t.ms) this else t

  def is_zero: Boolean = ms == 0
  def is_relevant: Boolean = ms >= 1

  override def toString = Time.print_seconds(seconds)

  def message: String = toString + "s"
}

