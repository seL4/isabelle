/*
 * Prover commands with semantic state
 *
 * @author Johannes Hölzl, TU Munich
 * @author Fabian Immler, TU Munich
 */

package isabelle.prover


import javax.swing.text.Position
import javax.swing.tree.DefaultMutableTreeNode

import isabelle.proofdocument.Token
import isabelle.jedit.{Isabelle, Plugin}
import isabelle.XML

import sidekick.{SideKickParsedData, IAsset}


object Command {
  object Status extends Enumeration {
    val UNPROCESSED = Value("UNPROCESSED")
    val FINISHED = Value("FINISHED")
    val REMOVE = Value("REMOVE")
    val REMOVED = Value("REMOVED")
    val FAILED = Value("FAILED")
  }
}


class Command(val document: Document, val first: Token, val last: Token)
{
  val id = Isabelle.plugin.id()
  
  {
    var t = first
    while (t != null) {
      t.command = this
      t = if (t == last) null else t.next
    }
  }


  /* command status */

  private var _status = Command.Status.UNPROCESSED
  def status = _status
  def status_=(st: Command.Status.Value) = {
    if (st == Command.Status.UNPROCESSED) {
      // delete markup
      for (child <- root_node.children) {
        child.children = Nil
      }
    }
    _status = st
  }


  /* accumulated results */

  var results: List[XML.Tree] = Nil

  def results_xml = XML.document(
    results match {
      case Nil => XML.Elem("message", Nil, Nil)
      case List(elem) => elem
      case _ => XML.Elem("messages", Nil, List(results.first, results.last))
    }, "style")
  def add_result(tree: XML.Tree) {
    results = results ::: List(tree)    // FIXME canonical reverse order
  }


  /* content */

  def content(): String = document.getContent(this)

  def next = if (last.next != null) last.next.command else null
  def previous = if (first.previous != null) first.previous.command else null

  def start = first.start
  def stop = last.stop

  def proper_start = start
  def proper_stop = {
    var i = last
    while (i != first && i.kind.equals(Token.Kind.COMMENT))
      i = i.previous
    i.stop
  }


  /* markup tree */

  val root_node =
    new MarkupNode(this, 0, stop - start, id, Markup.COMMAND_SPAN, content())

  def node_from(kind: String, begin: Int, end: Int) = {
    val markup_content = /*content.substring(begin, end)*/ ""
    new MarkupNode(this, begin, end, id, kind, markup_content)
  }
}
