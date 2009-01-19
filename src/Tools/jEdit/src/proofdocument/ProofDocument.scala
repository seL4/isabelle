/*
 * Document as list of commands, consisting of lists of tokens
 *
 * @author Johannes Hölzl, TU Munich
 * @author Makarius
 */

package isabelle.proofdocument


import java.util.regex.Pattern
import isabelle.prover.{Prover, Command}


class StructureChange(
  val beforeChange: Command,
  val addedCommands: List[Command],
  val removedCommands: List[Command])

object ProofDocument
{
  // Be carefully when changing this regex. Not only must it handle the 
  // spurious end of a token but also:  
  // Bug ID: 5050507 Pattern.matches throws StackOverflow Error
  // http://bugs.sun.com/bugdatabase/view_bug.do?bug_id=5050507
  
  val token_pattern = 
    Pattern.compile(
      "\\{\\*([^*]|\\*[^}]|\\*\\z)*(\\z|\\*\\})|" +
      "\\(\\*([^*]|\\*[^)]|\\*\\z)*(\\z|\\*\\))|" +
      "(\\?'?|')[A-Za-z_0-9.]*|" + 
      "[A-Za-z_0-9.]+|" + 
      "[!#$%&*+-/<=>?@^_|~]+|" +
      "\"([^\\\\\"]?(\\\\(.|\\z))?)*+(\"|\\z)|" +
      "`([^\\\\`]?(\\\\(.|\\z))?)*+(`|\\z)|" +
      "[()\\[\\]{}:;]", Pattern.MULTILINE)

}

class ProofDocument(text: Text, prover: Prover)
{
  private var active = false 
  def activate() {
    if (!active) {
      active = true
      text_changed(0, text.length, 0)
    }
  }

  text.changes += (changed => text_changed(changed.start, changed.added, changed.removed))



  /** token view **/

  protected var firstToken: Token = null
  protected var lastToken: Token = null
  
  protected def tokens(start: Token, stop: Token) = new Iterator[Token] {
      var current = start
      def hasNext = current != stop && current != null
      def next() = { val save = current ; current = current.next ; save }
    }
  protected def tokens(start: Token): Iterator[Token] = tokens(start, null)
  protected def tokens() : Iterator[Token] = tokens(firstToken, null)


  private def text_changed(start: Int, addedLen: Int, removedLen: Int)
  {
    if (!active)
      return

    var beforeChange = 
      if (Token.check_stop(firstToken, _ < start)) Token.scan(firstToken, _.stop >= start)
      else null
    
    var firstRemoved = 
      if (beforeChange != null) beforeChange.next
      else if (Token.check_start(firstToken, _ <= start + removedLen)) firstToken
      else null 

    var lastRemoved = Token.scan(firstRemoved, _.start > start + removedLen)

    var shiftToken = 
      if (lastRemoved != null) lastRemoved
      else if (Token.check_start(firstToken, _ > start)) firstToken
      else null
    
    while (shiftToken != null) {
      shiftToken.shift(addedLen - removedLen, start)
      shiftToken = shiftToken.next
    }
    
    // scan changed tokens until the end of the text or a matching token is
    // found which is beyond the changed area
    val matchStart = if (beforeChange == null) 0 else beforeChange.stop
    var firstAdded: Token = null
    var lastAdded: Token = null

    val matcher = ProofDocument.token_pattern.matcher(text.content(matchStart, text.length))
    var finished = false
    var position = 0 
    while (matcher.find(position) && ! finished) {
      position = matcher.end()
			val kind =
        if (prover.is_command_keyword(matcher.group()))
          Token.Kind.COMMAND_START
        else if (matcher.end() - matcher.start() > 2 && matcher.group().substring(0, 2) == "(*")
          Token.Kind.COMMENT
        else
          Token.Kind.OTHER
      val newToken = new Token(matcher.start() + matchStart, matcher.end() + matchStart, kind)

      if (firstAdded == null)
        firstAdded = newToken
      else {
        newToken.prev = lastAdded
        lastAdded.next = newToken
      }
      lastAdded = newToken
      
      while (Token.check_stop(lastRemoved, _ < newToken.stop) &&
              lastRemoved.next != null)	
        lastRemoved = lastRemoved.next
			
      if (newToken.stop >= start + addedLen && 
            Token.check_stop(lastRemoved, _ == newToken.stop))
        finished = true
    }

    var afterChange = if (lastRemoved != null) lastRemoved.next else null
		
    // remove superflous first token-change
    if (firstAdded != null && firstAdded == firstRemoved && 
          firstAdded.stop < start) {
      beforeChange = firstRemoved
      if (lastRemoved == firstRemoved) {
        lastRemoved = null
        firstRemoved = null
      }
      else {
        firstRemoved = firstRemoved.next
        assert(firstRemoved != null)
      }

      if (lastAdded == firstAdded) {
        lastAdded = null
        firstAdded = null
      }
      if (firstAdded != null)
        firstAdded = firstAdded.next
    }
    
    // remove superflous last token-change
    if (lastAdded != null && lastAdded == lastRemoved &&
          lastAdded.start > start + addedLen) {
      afterChange = lastRemoved
      if (firstRemoved == lastRemoved) {
        firstRemoved = null
        lastRemoved = null
      }
      else {
        lastRemoved = lastRemoved.prev
        assert(lastRemoved != null)
      }
      
      if (lastAdded == firstAdded) {
        lastAdded = null
        firstAdded = null
      }
      else
        lastAdded = lastAdded.prev
    }
    
    if (firstRemoved == null && firstAdded == null)
      return
    
    if (firstToken == null) {
      firstToken = firstAdded
      lastToken = lastAdded
    }
    else {
      // cut removed tokens out of list
      if (firstRemoved != null)
        firstRemoved.prev = null
      if (lastRemoved != null)
        lastRemoved.next = null
      
      if (firstToken == firstRemoved)
        if (firstAdded != null)
          firstToken = firstAdded
        else
          firstToken = afterChange
      
      if (lastToken == lastRemoved)
        if (lastAdded != null)
          lastToken = lastAdded
        else
          lastToken = beforeChange
      
      // insert new tokens into list
      if (firstAdded != null) {
        firstAdded.prev = beforeChange
        if (beforeChange != null)
          beforeChange.next = firstAdded
        else
          firstToken = firstAdded
      }
      else if (beforeChange != null)
        beforeChange.next = afterChange
      
      if (lastAdded != null) {
        lastAdded.next = afterChange
        if (afterChange != null)
          afterChange.prev = lastAdded
        else
          lastToken = lastAdded
      }
      else if (afterChange != null)
        afterChange.prev = beforeChange
    }
    
    token_changed(beforeChange, afterChange, firstRemoved)
  }
  

  
  /** command view **/

  val structural_changes = new EventBus[StructureChange]

  def commands = new Iterator[Command] {
    var current = firstToken
    def hasNext = current != null
    def next() = { val s = current.command ; current = s.last.next ; s }
  }

  def getContent(cmd: Command) = text.content(cmd.proper_start, cmd.proper_stop)

  def getNextCommandContaining(pos: Int): Command = {
    for (cmd <- commands) { if (pos < cmd.stop) return cmd }
    return null
  }

  private def token_changed(start: Token, stop: Token, removed: Token)
  {
    var removedCommands: List[Command] = Nil
    var first: Command = null
    var last: Command = null

    for(t <- tokens(removed)) {
      if (first == null)
        first = t.command
      if (t.command != last)
        removedCommands = t.command :: removedCommands
      last = t.command
    }

    var before: Command = null
    if (!removedCommands.isEmpty) {
      if (first.first == removed) {
        if (start == null)
          before = null
        else
          before = start.command
      }
      else
        before = first.prev
    }

    var addedCommands: List[Command] = Nil
    var scan: Token = null
    if (start != null) {
      val next = start.next
      if (first != null && first.first != removed) {
        scan = first.first
        if (before == null)
          before = first.prev
      }
      else if (next != null && next != stop) {
        if (next.kind == Token.Kind.COMMAND_START) {
          before = start.command
          scan = next
        }
        else if (first == null || first.first == removed) {
          first = start.command
          removedCommands = first :: removedCommands
          scan = first.first
          if (before == null)
            before = first.prev
        }
        else {
          scan = first.first
          if (before == null)
            before = first.prev
        }
      }
    }
    else
      scan = firstToken

    var stopScan: Token = null
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

    var cmdStart: Token = null
    var cmdStop: Token = null
    var overrun = false
    var finished = false
    while (scan != null && !finished) {
      if (scan == stopScan) {
        if (scan.kind == Token.Kind.COMMAND_START)
          finished = true
        else
          overrun = true
      }

      if (scan.kind == Token.Kind.COMMAND_START && cmdStart != null && !finished) {
        if (!overrun) {
          addedCommands = new Command(this, cmdStart, cmdStop) :: addedCommands
          cmdStart = scan
          cmdStop = scan
        }
        else
          finished = true
      }
      else if (!finished) {
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

    structural_changes.event(new StructureChange(before, addedCommands, removedCommands))
  }
}
