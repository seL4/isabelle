/*
 * Prover commands with semantic state
 *
 * @author Johannes Hölzl, TU Munich
 * @author Fabian Immler, TU Munich
 */

package isabelle.prover


import javax.swing.text.Position
import javax.swing.tree.DefaultMutableTreeNode

import scala.collection.mutable

import isabelle.proofdocument.{Text, Token, ProofDocument}
import isabelle.jedit.{Isabelle, Plugin}
import isabelle.XML

import sidekick.{SideKickParsedData, IAsset}


object Command {
  object Status extends Enumeration {
    val UNPROCESSED = Value("UNPROCESSED")
    val FINISHED = Value("FINISHED")
    val FAILED = Value("FAILED")
  }
}


class Command(val tokens: List[Token], val starts: Map[Token, Int])
{
  val id = Isabelle.plugin.id()

  /* content */

  override def toString = name

  val name = tokens.head.content
  val content:String = Token.string_from_tokens(tokens, starts)

  def start(doc: ProofDocument) = doc.token_start(tokens.first)
  def stop(doc: ProofDocument) = doc.token_start(tokens.last) + tokens.last.length

  /* command status */

  var state_id: IsarDocument.State_ID = null

  private var _status = Command.Status.UNPROCESSED
  def status = _status
  def status_=(st: Command.Status.Value) {
    if (st == Command.Status.UNPROCESSED) {
      state_results.clear
      // delete markup
      markup_root.filter(_.info match {
          case RootInfo() | OuterInfo(_) => true
          case _ => false
        })
    }
    _status = st
  }


  /* results */

  private val results = new mutable.ListBuffer[XML.Tree]
  private val state_results = new mutable.ListBuffer[XML.Tree]
  def add_result(running: Boolean, tree: XML.Tree) = synchronized {
    (if (running) state_results else results) += tree
  }

  def result_document = XML.document(
    results.toList ::: state_results.toList match {
      case Nil => XML.Elem("message", Nil, Nil)
      case List(elem) => elem
      case elems => XML.Elem("messages", Nil, elems)
    }, "style")


  /* markup */

  val empty_root_node =
    new MarkupNode(this, 0, starts(tokens.last) - starts(tokens.first) + tokens.last.length, Nil,
                   id, content, RootInfo())

  var markup_root = empty_root_node

  def highlight_node: MarkupNode = {
    import MarkupNode._
    markup_root.filter(_.info match {
      case RootInfo() | OuterInfo(_) | HighlightInfo(_) => true
      case _ => false
    }).head
  }

  def markup_node(begin: Int, end: Int, info: MarkupInfo) =
    new MarkupNode(this, begin, end, Nil, id,
                   if (end <= content.length && begin >= 0) content.substring(begin, end) else "wrong indices??",
                   info)

  def type_at(pos: Int): String = {
    val types = markup_root.filter(_.info match {case TypeInfo(_) => true case _ => false})
    types.flatten(_.flatten).
      find(t => t.start <= pos && t.stop > pos).
      map(t => "\"" + t.content + "\" : " + (t.info match {case TypeInfo(i) => i case _ => ""})).
      getOrElse(null)
  }

  def ref_at(pos: Int): Option[MarkupNode] =
    markup_root.filter(_.info match {case RefInfo(_,_,_,_) => true case _ => false}).
      flatten(_.flatten).
      find(t => t.start <= pos && t.stop > pos)
}
