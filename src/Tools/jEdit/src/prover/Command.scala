/*
 * Prover commands with semantic state
 *
 * @author Johannes Hölzl, TU Munich
 * @author Fabian Immler, TU Munich
 */

package isabelle.prover


import scala.actors.Actor, Actor._

import scala.collection.mutable

import isabelle.proofdocument.{Token, ProofDocument}
import isabelle.jedit.{Isabelle, Plugin}
import isabelle.XML


trait Accumulator extends Actor
{

  start() // start actor

  protected var _state: State
  def state = _state

  override def act() {
    loop {
      react {
        case message: XML.Tree => _state += message
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


class Command(
  val tokens: List[Token],
  val starts: Map[Token, Int],
  change_receiver: Actor) extends Accumulator
{
  require(!tokens.isEmpty)

  val id = Isabelle.system.id()
  override def hashCode = id.hashCode

  def changed() = change_receiver ! this


  /* content */

  override def toString = name

  val name = tokens.head.content
  val content: String = Token.string_from_tokens(tokens, starts)
  val symbol_index = new Symbol.Index(content)

  def start(doc: ProofDocument) = doc.token_start(tokens.first)
  def stop(doc: ProofDocument) = doc.token_start(tokens.last) + tokens.last.length

  def contains(p: Token) = tokens.contains(p)

  protected override var _state = new State(this)


  /* markup */

  lazy val empty_root_node =
    new MarkupNode(0, starts(tokens.last) - starts(tokens.first) + tokens.last.length,
      Nil, content, RootInfo())

  def markup_node(begin: Int, end: Int, info: MarkupInfo): MarkupNode =
  {
    val start = symbol_index.decode(begin)
    val stop = symbol_index.decode(end)
    new MarkupNode(start, stop, Nil, content.substring(start, stop), info)
  }


  /* results, markup, ... */

  private val empty_cmd_state = new Command_State(this)
  private def cmd_state(doc: ProofDocument) =
    doc.states.getOrElse(this, empty_cmd_state)

  def status(doc: ProofDocument) = cmd_state(doc).state.status
  def result_document(doc: ProofDocument) = cmd_state(doc).result_document
  def markup_root(doc: ProofDocument) = cmd_state(doc).markup_root
  def highlight_node(doc: ProofDocument) = cmd_state(doc).highlight_node
  def type_at(doc: ProofDocument, offset: Int) = cmd_state(doc).type_at(offset)
  def ref_at(doc: ProofDocument, offset: Int) = cmd_state(doc).ref_at(offset)
}


class Command_State(val command: Command) extends Accumulator
{
  protected override var _state = new State(command)

  def result_document: org.w3c.dom.Document =
    XML.document(
      command.state.results ::: state.results match {
        case Nil => XML.Elem("message", Nil, Nil)
        case List(elem) => elem
        case elems => XML.Elem("messages", Nil, elems)
      }, "style")

  def markup_root: MarkupNode =
    (command.state.markup_root /: state.markup_root.children)(_ + _)

  def type_at(pos: Int): String = state.type_at(pos)

  def ref_at(pos: Int): Option[MarkupNode] = state.ref_at(pos)

  def highlight_node: MarkupNode =
    (command.state.highlight_node /: state.highlight_node.children)(_ + _)
}