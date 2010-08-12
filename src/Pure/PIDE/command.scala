/*  Title:      Pure/PIDE/command.scala
    Author:     Johannes Hölzl, TU Munich
    Author:     Fabian Immler, TU Munich
    Author:     Makarius

Prover commands with semantic state.
*/

package isabelle


import scala.actors.Actor, Actor._
import scala.collection.mutable


object Command
{
  object Status extends Enumeration
  {
    val UNPROCESSED = Value("UNPROCESSED")
    val FINISHED = Value("FINISHED")
    val FAILED = Value("FAILED")
    val UNDEFINED = Value("UNDEFINED")
  }

  case class HighlightInfo(kind: String, sub_kind: Option[String]) {
    override def toString = kind
  }
  case class TypeInfo(ty: String)
  case class RefInfo(file: Option[String], line: Option[Int],
    command_id: Option[Document.Command_ID], offset: Option[Int])  // FIXME Command_ID vs. State_ID !?
}

class Command(
    val id: Document.Command_ID,
    val span: Thy_Syntax.Span,
    val static_parent: Option[Command] = None)  // FIXME !?
  extends Session.Entity
{
  /* classification */

  def is_command: Boolean = !span.isEmpty && span.head.is_command
  def is_ignored: Boolean = span.forall(_.is_ignored)
  def is_malformed: Boolean = !is_command && !is_ignored

  def name: String = if (is_command) span.head.content else ""
  override def toString =
    id + "/" + (if (is_command) name else if (is_ignored) "IGNORED" else "MALFORMED")


  /* source text */

  val source: String = span.map(_.source).mkString
  def source(i: Int, j: Int): String = source.substring(i, j)
  def length: Int = source.length

  lazy val symbol_index = new Symbol.Index(source)


  /* accumulated messages */

  @volatile protected var state = new State(this)
  def current_state: State = state

  private case class Consume(message: XML.Tree, forward: Command => Unit)
  private case object Assign

  private val accumulator = actor {
    var assigned = false
    loop {
      react {
        case Consume(message, forward) if !assigned =>
          val old_state = state
          state = old_state.accumulate(message)
          if (!(state eq old_state)) forward(static_parent getOrElse this)

        case Assign =>
          assigned = true  // single assignment
          reply(())

        case bad => System.err.println("Command accumulator: ignoring bad message " + bad)
      }
    }
  }

  def consume(message: XML.Tree, forward: Command => Unit)
  {
    accumulator ! Consume(message, forward)
  }

  def assign_state(state_id: Document.State_ID): Command =
  {
    val cmd = new Command(state_id, span, Some(this))
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
