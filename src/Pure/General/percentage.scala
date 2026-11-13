/*  Title:      Pure/General/percentage.scala
    Author:     Makarius

Percentage: precision in permille.
*/

package isabelle


object Percentage {
  def permille(permille: Int): Percentage = new Percentage(permille)
  val zero: Percentage = permille(0)

  def apply(a: Long, b: Long): Percentage =
    new Percentage(if (b == 0L) 0 else ((a.toDouble / b.toDouble) * 1000.0).round.toInt)

  def apply(a: Int, b: Int): Percentage = apply(a.toLong, b.toLong)

  def space(a: Space, b: Space): Percentage = apply(a.bytes, b.bytes)
}

final class Percentage private(val permille: Int) extends AnyVal {
  def percent: Double = permille.toDouble / 10

  override def toString: String = (permille / 10).toString + "." + (permille % 10).toString + "%"
}

