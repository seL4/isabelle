/*
 * Prover commands with semantic state
 *
 * @author Johannes Hölzl, TU Munich
 * @author Fabian Immler, TU Munich
 */

package isabelle.prover

import isabelle.proofdocument.Token
import isabelle.jedit.Plugin
import isabelle.{ YXML, XML }
import sidekick.{SideKickParsedData, IAsset}
import javax.swing.text.Position
import javax.swing.tree.DefaultMutableTreeNode

object Command {
  object Phase extends Enumeration {
    val UNPROCESSED = Value("UNPROCESSED")
    val FINISHED = Value("FINISHED")
    val REMOVE = Value("REMOVE")
    val REMOVED = Value("REMOVED")
    val FAILED = Value("FAILED")
  }

  private var nextId : Long = 0
  def generateId : Long = {
    nextId = nextId + 1
    return nextId
  }
  
  def idFromString(id : String) = Long.unbox(java.lang.Long.valueOf(id, 36))
}

class Command(val document : Document, val first : Token[Command], val last : Token[Command]) {
  import Command._
  
  {
    var t = first
    while(t != null) {
      t.command = this
      t = if (t == last) null else t.next
    }
  }
  
  val id : Long = generateId

  private var p = Phase.UNPROCESSED
  def phase = p
  def phase_=(p_new : Phase.Value) = {
    if(p_new == Phase.UNPROCESSED){
      //delete inner syntax
      for(child <- root_node.children){
        child.children = Nil
      }
    }
    p = p_new
  }
	
  var results = Nil : List[XML.Tree]

  def idString = java.lang.Long.toString(id, 36)
  def results_xml = XML.document(
    results match {
      case Nil => XML.Elem("message", Nil, Nil)
      case List(elem) => elem
      case _ =>
        XML.Elem("messages", List(), List(results.first, results.last))
    }, "style")
  def addResult(tree : XML.Tree) {
    results = results ::: List(tree)    // FIXME canonical reverse order
  }
  
  val root_node = 
    new MarkupNode(this, 0, stop - start, idString, "Command", document.getContent(this))

  def node_from(kind : String, begin : Int, end : Int) : MarkupNode = {
    val markup_content = /*content.substring(begin, end)*/ ""
    new MarkupNode(this, begin, end, idString, kind, markup_content)
  }

  def content = document.getContent(this)

  def next = if (last.next != null) last.next.command else null
  def previous = if (first.previous != null) first.previous.command else null

  def start = first start
  def stop = last stop
  
  def properStart = start
  def properStop = {
    var i = last
    while (i != first && i.kind.equals(Token.Kind.COMMENT))
      i = i.previous
    i.stop
  }  	
}