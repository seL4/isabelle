/*
 * Prover commands with semantic state
 *
 * @author Johannes Hölzl, TU Munich
 * @author Fabian Immler, TU Munich
 */

package isabelle.prover


import scala.actors.Actor
import scala.actors.Actor._

import scala.collection.mutable

import isabelle.proofdocument.{Token, ProofDocument}
import isabelle.jedit.{Isabelle, Plugin}
import isabelle.XML

import sidekick.{SideKickParsedData, IAsset}

trait Accumulator extends Actor
{

  start() // start actor

  protected var _state: State
  def state = _state

  override def act() {
    loop {
      react {
        case x: XML.Tree => _state += x
      }
    }
  }
}


object Command
{
  object Status extends Enumeration
  {
    val UNPROCESSED = Value("UNPROCESSED")
    val FINISHED = Value("FINISHED")
    val FAILED = Value("FAILED")
  }
}


class Command(val tokens: List[Token], val starts: Map[Token, Int], chg_rec: Actor)
{
  require(!tokens.isEmpty)

  val id = Isabelle.system.id()
  override def hashCode = id.hashCode

  def changed() = chg_rec ! this


  /* content */

  override def toString = name

  val name = tokens.head.content
  val content: String = Token.string_from_tokens(tokens, starts)
  val symbol_index = new Symbol.Index(content)

  def start(doc: ProofDocument) = doc.token_start(tokens.first)
  def stop(doc: ProofDocument) = doc.token_start(tokens.last) + tokens.last.length

  def contains(p: Token) = tokens.contains(p)

  /* states */
  val states = mutable.Map[IsarDocument.State_ID, Command_State]()
  private def state(doc: ProofDocument) = doc.states.get(this)
  
  /* command status */

  def set_status(state: IsarDocument.State_ID, status: Command.Status.Value) = {
    if (state != null)
      states.getOrElseUpdate(state, new Command_State(this)).status = status
  }

  def status(doc: ProofDocument) =
    state(doc) match {
      case Some(s) => states.getOrElseUpdate(s, new Command_State(this)).status
      case _ => Command.Status.UNPROCESSED
    }

  /* results */

  private val results = new mutable.ListBuffer[XML.Tree]
  def add_result(state: IsarDocument.State_ID, tree: XML.Tree) = synchronized {
    (if (state == null) results else states(state).results) += tree
  }

  def result_document(doc: ProofDocument) = {
    val state_results = state(doc) match {
      case Some(s) =>
        states.getOrElseUpdate(s, new Command_State(this)).results
      case _ => Nil}
    XML.document(
      results.toList ::: state_results.toList match {
        case Nil => XML.Elem("message", Nil, Nil)
        case List(elem) => elem
        case elems => XML.Elem("messages", Nil, elems)
      }, "style")
  }


  /* markup */

  val empty_root_node =
    new MarkupNode(this, 0, starts(tokens.last) - starts(tokens.first) + tokens.last.length,
      Nil, id, content, RootInfo())
  private var _markup_root = empty_root_node
  def add_markup(state: IsarDocument.State_ID, raw_node: MarkupNode) = {
    // decode node
    val node = raw_node transform symbol_index.decode
    if (state == null) _markup_root += node
    else {
      val cmd_state = states.getOrElseUpdate(state, new Command_State(this))
      cmd_state.markup_root += node
    }
  }

  def markup_root(doc: ProofDocument): MarkupNode = {
    state(doc) match {
      case Some(s) =>
        (_markup_root /: states(s).markup_root.children) (_ + _)
      case _ => _markup_root
    }
  }

  def highlight_node(doc: ProofDocument): MarkupNode =
  {
    import MarkupNode._
    markup_root(doc).filter(_.info match {
      case RootInfo() | OuterInfo(_) | HighlightInfo(_) => true
      case _ => false
    }).head
  }

  def markup_node(begin: Int, end: Int, info: MarkupInfo) =
    new MarkupNode(this, begin, end, Nil, id,
      if (end <= content.length && begin >= 0) content.substring(begin, end)
      else "wrong indices??",
      info)

  def type_at(doc: ProofDocument, pos: Int) =
    state(doc).map(states(_).type_at(pos)).getOrElse(null)

  def ref_at(doc: ProofDocument, pos: Int) =
    state(doc).flatMap(states(_).ref_at(pos))

}

class Command_State(val cmd: Command) {

  var status = Command.Status.UNPROCESSED

  /* results */
  val results = new mutable.ListBuffer[XML.Tree]

  /* markup */
  val empty_root_node = cmd.empty_root_node
  var markup_root = empty_root_node

  def type_at(pos: Int): String =
  {
    val types = markup_root.filter(_.info match { case TypeInfo(_) => true case _ => false })
    types.flatten(_.flatten).
      find(t => t.start <= pos && t.stop > pos).
      map(t => t.content + ": " + (t.info match { case TypeInfo(i) => i case _ => "" })).
      getOrElse(null)
  }

  def ref_at(pos: Int): Option[MarkupNode] =
    markup_root.filter(_.info match { case RefInfo(_, _, _, _) => true case _ => false }).
      flatten(_.flatten).
      find(t => t.start <= pos && t.stop > pos)
}
