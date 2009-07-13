/*
 * Changes in text as event
 *
 * @author Johannes Hölzl, TU Munich
 */

package isabelle.proofdocument


object Text {
  case class Change(
    base: Option[Change],
    id: String,
    start: Int,
    added: String,
    removed: String)
  {
    override def toString = id + ": added '" + added + "'; removed '" + removed + "'"

    def ancestors: List[Text.Change] =
      this :: base.map(_.ancestors).getOrElse(Nil)
  }
}
