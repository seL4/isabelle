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
import isabelle.XML


trait Accumulator extends Actor
{
  start() // start actor

  protected var _state: State
  def state = _state

  override def act() {
    loop {
      react {
        case (session: Session, message: XML.Tree) => _state = _state.+(session, message)
        case bad => System.err.println("Accumulator: ignoring bad message " + bad)
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

  case class HighlightInfo(highlight: String) { override def toString = highlight }
  case class TypeInfo(ty: String)
  case class RefInfo(file: Option[String], line: Option[Int],
    command_id: Option[String], offset: Option[Int])
}


class Command(
    val id: String,
    val tokens: List[Token],
    val starts: Map[Token, Int]) extends Accumulator
{
  require(!tokens.isEmpty)

  override def hashCode = id.hashCode


  /* content */

  override def toString = name

  val name = tokens.head.content
  val content: String = Token.string_from_tokens(tokens, starts)
  def content(i: Int, j: Int): String = content.substring(i, j)
  val symbol_index = new Symbol.Index(content)

  def start(doc: Proof_Document) = doc.token_start(tokens.first)
  def stop(doc: Proof_Document) = doc.token_start(tokens.last) + tokens.last.length

  def contains(p: Token) = tokens.contains(p)

  protected override var _state = new State(this)


  /* markup */

  lazy val empty_markup = new Markup_Text(Nil, content)

  def markup_node(begin: Int, end: Int, info: Any): Markup_Tree =
  {
    val start = symbol_index.decode(begin)
    val stop = symbol_index.decode(end)
    new Markup_Tree(new Markup_Node(start, stop, info), Nil)
  }


  /* results, markup, ... */

  private val empty_cmd_state = new Command_State(this)
  private def cmd_state(doc: Proof_Document) =
    doc.states.getOrElse(this, empty_cmd_state)

  def status(doc: Proof_Document) = cmd_state(doc).state.status
  def results(doc: Proof_Document) = cmd_state(doc).results
  def markup_root(doc: Proof_Document) = cmd_state(doc).markup_root
  def highlight(doc: Proof_Document) = cmd_state(doc).highlight
  def type_at(doc: Proof_Document, offset: Int) = cmd_state(doc).type_at(offset)
  def ref_at(doc: Proof_Document, offset: Int) = cmd_state(doc).ref_at(offset)
}


class Command_State(val command: Command) extends Accumulator
{
  protected override var _state = new State(command)

  def results: List[XML.Tree] =
    command.state.results ::: state.results

  def markup_root: Markup_Text =
    (command.state.markup_root /: state.markup_root.markup)(_ + _)

  def type_at(pos: Int): Option[String] = state.type_at(pos)

  def ref_at(pos: Int): Option[Markup_Node] = state.ref_at(pos)

  def highlight: Markup_Text =
    (command.state.highlight /: state.highlight.markup)(_ + _)
}