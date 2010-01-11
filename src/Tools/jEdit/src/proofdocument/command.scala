/*
 * Prover commands with semantic state
 *
 * @author Johannes Hölzl, TU Munich
 * @author Fabian Immler, TU Munich
 */

package isabelle.proofdocument


import scala.actors.Actor, Actor._
import scala.collection.mutable

import isabelle.jedit.Isabelle


object Command
{
  object Status extends Enumeration
  {
    val UNPROCESSED = Value("UNPROCESSED")
    val FINISHED = Value("FINISHED")
    val FAILED = Value("FAILED")
  }

  case class HighlightInfo(highlight: String) { override def toString = highlight }
  case class TypeInfo(ty: String)
  case class RefInfo(file: Option[String], line: Option[Int],
    command_id: Option[String], offset: Option[Int])
}


class Command(
    val id: Isar_Document.Command_ID,
    val span: Thy_Syntax.Span)
  extends Session.Entity
{
  /* classification */

  def is_command: Boolean = !span.isEmpty && span.first.is_command
  def is_ignored: Boolean = span.forall(_.is_ignored)
  def is_malformed: Boolean = !is_command && !is_ignored

  def name: String = if (is_command) span.first.content else ""
  override def toString = if (is_command) name else if (is_ignored) "<ignored>" else "<malformed>"


  /* source text */

  val source: String = span.map(_.source).mkString
  def source(i: Int, j: Int): String = source.substring(i, j)
  def length: Int = source.length

  lazy val symbol_index = new Symbol.Index(source)


  /* accumulated messages */

  @volatile protected var state = new State(this)
  def current_state: State = state

  private case class Consume(session: Session, message: XML.Tree)
  private case object Assign

  private val accumulator = actor {
    var assigned = false
    loop {
      react {
        case Consume(session: Session, message: XML.Tree) if !assigned =>
          state = state.+(session, message)

        case Assign =>
          assigned = true  // single assignment
          reply(())

        case bad => System.err.println("command accumulator: ignoring bad message " + bad)
      }
    }
  }

  def consume(session: Session, message: XML.Tree) { accumulator ! Consume(session, message) }

  def assign_state(state_id: Isar_Document.State_ID): Command =
  {
    val cmd = new Command(state_id, span)
    accumulator !? Assign
    cmd.state = current_state
    cmd
  }


  /* markup */

  lazy val empty_markup = new Markup_Text(Nil, source)

  def markup_node(begin: Int, end: Int, info: Any): Markup_Tree =
  {
    val start = symbol_index.decode(begin)
    val stop = symbol_index.decode(end)
    new Markup_Tree(new Markup_Node(start, stop, info), Nil)
  }
}
