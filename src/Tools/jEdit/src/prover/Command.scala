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


class Command(val tokens: List[Token])
{
  val id = Isabelle.plugin.id()

  /* content */

  override def toString = name

  val name = tokens.head.content
  val content:String = Token.string_from_tokens(tokens.takeWhile(_.kind != Token.Kind.COMMENT))

  def start = tokens.first.start
  def stop = tokens.last.stop

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
    new MarkupNode(this, 0, stop - start, id, Markup.COMMAND_SPAN, content)

  def node_from(kind: String, begin: Int, end: Int) = {
    val markup_content = content.substring(begin, end)
    new MarkupNode(this, begin, end, id, kind, markup_content)
  }
}
