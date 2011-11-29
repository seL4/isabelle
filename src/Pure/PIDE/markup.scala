/*  Title:      Pure/PIDE/markup.scala
    Module:     PIDE
    Author:     Makarius

Generic markup elements.
*/

package isabelle


object Markup
{
  /* properties */

  val NAME = "name"
  val Name = new Properties.String(NAME)

  val KIND = "kind"
  val Kind = new Properties.String(KIND)


  /* elements */

  val Empty = Markup("", Nil)
  val Data = Markup("data", Nil)
  val Broken = Markup("broken", Nil)


  /* timing */

  val TIMING = "timing"
  val ELAPSED = "elapsed"
  val CPU = "cpu"
  val GC = "gc"

  object Timing
  {
    def apply(timing: isabelle.Timing): Markup =
      Markup(TIMING, List(
        (ELAPSED, Properties.Value.Double(timing.elapsed.seconds)),
        (CPU, Properties.Value.Double(timing.cpu.seconds)),
        (GC, Properties.Value.Double(timing.gc.seconds))))
    def unapply(markup: Markup): Option[isabelle.Timing] =
      markup match {
        case Markup(TIMING, List(
          (ELAPSED, Properties.Value.Double(elapsed)),
          (CPU, Properties.Value.Double(cpu)),
          (GC, Properties.Value.Double(gc)))) =>
            Some(new isabelle.Timing(Time.seconds(elapsed), Time.seconds(cpu), Time.seconds(gc)))
        case _ => None
      }
  }
}


sealed case class Markup(name: String, properties: Properties.T)

