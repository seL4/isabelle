package isabelle.prover

import isabelle.proofdocument.Token
import isabelle.jedit.Plugin
import isabelle.{ YXML, XML }
import sidekick.{SideKickParsedData}
import sidekick.enhanced.SourceAsset
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
  var phase = Phase.UNPROCESSED
	
  var results = Nil : List[XML.Tree]

  //offsets relative to first.start!
  class Status(val kind : String,val start : Int, val stop : Int ) { }
  var statuses = Nil : List[Status]
  def statuses_xml = XML.Elem("statuses", List(), statuses.map (s => XML.Text(s.kind + ": " + s.start + "-" + s.stop + "\n")))

  def idString = java.lang.Long.toString(id, 36)
  def results_xml = XML.document(results match {
                                case Nil => XML.Elem("message", List(), List())
                                case List(elem) => elem
                                case _ =>
                                  XML.Elem("messages", List(), List(results.first,
                                                                    results.last))
                              }, "style")
  def addResult(tree : XML.Tree) {
    results = results ::: List(tree)
  }
  
  val root_node = {
    val content = document.getContent(this)
    val ra = new RelativeAsset(this, 0, stop - start, "command", content)
    new DefaultMutableTreeNode(ra)
  }

  // does cand fit into node?
  private def fitting(cand : DefaultMutableTreeNode, node : DefaultMutableTreeNode) : boolean = {
    val node_asset = node.getUserObject.asInstanceOf[RelativeAsset]
    val n_start = node_asset.rel_start
    val n_end = node_asset.rel_end
    val cand_asset = cand.getUserObject.asInstanceOf[RelativeAsset]
    val c_start = cand_asset.rel_start
    val c_end = cand_asset.rel_end
    System.err.println(c_start - n_start + " " + (c_end - n_end))
    return c_start >= n_start && c_end <= n_end
  }

  def insert_node(new_node : DefaultMutableTreeNode, node : DefaultMutableTreeNode) {
    assert(fitting(new_node, node))
    val children = node.children
    while (children.hasMoreElements){
      val child = children.nextElement.asInstanceOf[DefaultMutableTreeNode]
      if(fitting(new_node, child)) {
        insert_node(new_node, child)
      }
    }
    if(new_node.getParent == null){
      while(children.hasMoreElements){
        val child = children.nextElement.asInstanceOf[DefaultMutableTreeNode]
        if(fitting(child, new_node)) {
          node.remove(child.asInstanceOf[DefaultMutableTreeNode])
          new_node.add(child)
        }
      }
      node.add(new_node)
    }
  }

 def addStatus(tree : XML.Tree) {
    val (state, attr) = tree match { case XML.Elem("message", _, XML.Elem(kind, attr, _) :: _) => (kind, attr)
                                   case _ => null}
    if (phase != Phase.REMOVED && phase != Phase.REMOVE) {
      state match {
        case "finished" =>
          phase = Phase.FINISHED
        case "unprocessed" =>
          phase = Phase.UNPROCESSED
        case "failed" =>
          phase = Phase.FAILED
        case "removed" =>
          // TODO: never lose information on command + id ??
          //document.prover.commands.removeKey(st.idString)
          phase = Phase.REMOVED
        case _ =>
          //process attributes:
          var markup_begin = -1
          var markup_end = -1
          for((n, a) <- attr) {
            if(n.equals("offset")) markup_begin = Int.unbox(java.lang.Integer.valueOf(a)) - 1
            if(n.equals("end_offset")) markup_end = Int.unbox(java.lang.Integer.valueOf(a)) - 1
          }
          if(markup_begin > -1 && markup_end > -1){
            statuses = new Status(state, markup_begin, markup_end) :: statuses
            val markup_content = content.substring(markup_begin, markup_end)
            val asset = new RelativeAsset(this, markup_begin, markup_end, state, markup_content)
            val new_node = new DefaultMutableTreeNode(asset)
            insert_node(new_node, root_node)
          } else {
            System.err.println("addStatus - ignored: " + tree)
          }
      }
    }
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