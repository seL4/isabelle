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
  val content:String = Token.string_from_tokens(tokens.takeWhile(_.kind != Token.Kind.COMMENT), starts)

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
      for (child <- root_node.children) {
        child.children = Nil
      }
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

  val root_node =
    new MarkupNode(this, 0, starts(tokens.last) - starts(tokens.first) + tokens.last.length, id, content, Markup.COMMAND_SPAN)

  def add_markup(desc: String, begin: Int, end: Int) = {
    val markup_content = if (end <= content.length) content.substring(begin, end)
      else {
        System.err.println (root_node.stop, content, content.length, end)
        "wrong indices?"
      }
    root_node insert new MarkupNode(this, begin, end, id, markup_content, desc)
  }

  // syntax highlighting
  val highlight_node =
   new MarkupNode(this, 0, starts(tokens.last) - starts(tokens.first) + tokens.last.length, id, content, Markup.COMMAND_SPAN)

  def add_highlight(kind: String, begin: Int, end: Int) =
    highlight_node insert new MarkupNode(this, begin, end, id, "", kind)

}
