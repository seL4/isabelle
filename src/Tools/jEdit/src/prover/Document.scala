/*
 * Document as list of commands
 *
 * @author Johannes Hölzl, TU Munich
 */

package isabelle.prover

import isabelle.proofdocument.{ProofDocument, Token, Text}


object Document {
  class StructureChange(val beforeChange : Command,
                        val addedCommands : List[Command],
                        val removedCommands : List[Command])
}


class Document(text : Text, val prover : Prover) extends ProofDocument(text)
{
  val structural_changes = new EventBus[Document.StructureChange]

  def isStartKeyword(s : String) = prover.command_decls.contains(s)

  def commands() = new Iterator[Command] {
    var current = firstToken
    def hasNext() = current != null
    def next() = { try {val s = current.command ; current = s.last.next ; s}
    catch { case error : NullPointerException =>
      System.err.println("NPE!")
      throw error
    }
    }
  }

  def getContent(cmd : Command) = text.content(cmd.proper_start, cmd.proper_stop)

  def getNextCommandContaining(pos : Int) : Command = {
    for( cmd <- commands()) { if (pos < cmd.stop) return cmd }
    return null
  }

  override def tokenChanged(start : Token, stop : Token, removed : Token)
  {
    var removedCommands : List[Command] = Nil
    var first : Command = null
    var last : Command = null

    for(t <- tokens(removed)) {
      if (first == null)
        first = t.command
      if (t.command != last)
        removedCommands = t.command :: removedCommands
      last = t.command
    }

    var before : Command = null
    if (! removedCommands.isEmpty) {
      if (first.first == removed) {
        if (start == null)
          before = null
        else
          before = start.command
      }
      else
        before = first.previous
    }

    var addedCommands : List[Command] = Nil
    var scan : Token = null
    if (start != null) {
      val next = start.next
      if (first != null && first.first != removed) {
        scan = first.first
        if (before == null)
          before = first.previous
      }
      else if (next != null && next != stop) {
        if (next.kind.equals(Token.Kind.COMMAND_START)) {
          before = start.command
          scan = next
        }
        else if (first == null || first.first == removed) {
          first = start.command
          removedCommands = first :: removedCommands
          scan = first.first
          if (before == null)
            before = first.previous
        }
        else {
          scan = first.first
          if (before == null)
            before = first.previous
        }
      }
    }
    else
      scan = firstToken

    var stopScan : Token = null
    if (stop != null) {
      if (stop == stop.command.first)
        stopScan = stop
      else
        stopScan = stop.command.last.next
    }
    else if (last != null)
      stopScan = last.last.next
    else
      stopScan = null

    var cmdStart : Token = null
    var cmdStop : Token = null
    var overrun = false
    var finished = false
    while (scan != null && !finished) {
      if (scan == stopScan) {
        if (scan.kind.equals(Token.Kind.COMMAND_START))
          finished = true
        else
          overrun = true
      }

      if (scan.kind.equals(Token.Kind.COMMAND_START) && cmdStart != null && !finished) {
        if (! overrun) {
          addedCommands = new Command(this, cmdStart, cmdStop) :: addedCommands
          cmdStart = scan
          cmdStop = scan
        }
        else
          finished = true
      }
      else if (! finished) {
        if (cmdStart == null)
          cmdStart = scan
        cmdStop = scan
      }
      if (overrun && !finished) {
        if (scan.command != last)
          removedCommands = scan.command :: removedCommands
        last = scan.command
      }

      if (!finished)
        scan = scan.next
    }

    if (cmdStart != null)
      addedCommands = new Command(this, cmdStart, cmdStop) :: addedCommands

    // relink commands
    addedCommands = addedCommands.reverse
    removedCommands = removedCommands.reverse

    structural_changes.event(
      new Document.StructureChange(before, addedCommands, removedCommands))
  }
}
