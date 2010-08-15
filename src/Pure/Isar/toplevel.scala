/*  Title:      Pure/Isar/toplevel.scala
    Author:     Makarius

Isabelle/Isar toplevel transactions.
*/

package isabelle


object Toplevel
{
  sealed abstract class Status
  case class Forked(forks: Int) extends Status
  case object Unprocessed extends Status
  case object Finished extends Status
  case object Failed extends Status

  def command_status(markup: List[Markup]): Status =
  {
    val forks = (0 /: markup) {
      case (i, Markup(Markup.FORKED, _)) => i + 1
      case (i, Markup(Markup.JOINED, _)) => i - 1
      case (i, _) => i
    }
    if (forks != 0) Forked(forks)
    else if (markup.exists(_.name == Markup.FAILED)) Failed
    else if (markup.exists(_.name == Markup.FINISHED)) Finished
    else Unprocessed
  }
}

