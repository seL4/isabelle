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

  def command_status(markup: XML.Body): Status =
  {
    val forks = (0 /: markup) {
      case (i, XML.Elem(Markup(Markup.FORKED, _), _)) => i + 1
      case (i, XML.Elem(Markup(Markup.JOINED, _), _)) => i - 1
      case (i, _) => i
    }
    if (forks != 0) Forked(forks)
    else if (markup.exists { case XML.Elem(Markup(Markup.FAILED, _), _) => true case _ => false })
      Failed
    else if (markup.exists { case XML.Elem(Markup(Markup.FINISHED, _), _) => true case _ => false })
      Finished
    else Unprocessed
  }
}

