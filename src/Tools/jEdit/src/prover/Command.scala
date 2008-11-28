package isabelle.prover

import isabelle.proofdocument.Token
import isabelle.{ YXML, XML }

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

class Command(val first : Token[Command], val last : Token[Command]) {
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
  
  def idString = java.lang.Long.toString(id, 36)
  def document = XML.document(results match {
                                case Nil => XML.Elem("message", List(), List())
                                case List(elem) => elem
                                case _ => 
                                  XML.Elem("messages", List(), List(results.first,
                                                                    results.last))
                              }, "style")
  def addResult(tree : XML.Tree) {
    results = results ::: List(tree)
  }

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