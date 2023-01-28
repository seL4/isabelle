/*  Title:      Pure/General/space.scala
    Author:     Makarius

Storage space based on bytes.
*/

package isabelle


import java.util.Locale

import scala.annotation.tailrec


object Space {
  def bytes(bs: Long): Space = new Space(bs)
  val zero: Space = bytes(0L)

  private val units: List[String] = List("B", "KiB", "MiB", "GiB", "TiB", "PiB", "EiB")

  def B(x: Double): Space = bytes(x.round)
  def KiB(x: Double): Space = B(x * 1024)
  def MiB(x: Double): Space = KiB(x * 1024)
  def GiB(x: Double): Space = MiB(x * 1024)
  def TiB(x: Double): Space = GiB(x * 1024)
  def PiB(x: Double): Space = TiB(x * 1024)
  def EiB(x: Double): Space = PiB(x * 1024)
}

final class Space private(val bytes: Long) extends AnyVal {
  def is_proper: Boolean = bytes > 0
  def is_relevant: Boolean = MiB >= 1.0

  def B: Double = bytes.toDouble
  def KiB: Double = B / 1024
  def MiB: Double = KiB / 1024
  def GiB: Double = MiB / 1024
  def TiB: Double = GiB / 1024
  def PiB: Double = TiB / 1024
  def EiB: Double = PiB / 1024

  override def toString: String = Value.Long(bytes)

  def print: String = {
    @tailrec def print_unit(x: Double, units: List[String]): String =
      if (x.abs < 1024 || units.tail.isEmpty) {
        val s = String.format(Locale.ROOT, "%.1f", x.asInstanceOf[AnyRef])
        Library.perhaps_unsuffix(".0", s) + " " + units.head
      }
      else print_unit(x / 1024, units.tail)

    print_unit(bytes.toDouble, Space.units)
  }

  def print_relevant: Option[String] = if (is_relevant) Some(print) else None
}
