/*
 * Document as list of commands, consisting of lists of tokens
 *
 * @author Johannes Hölzl, TU Munich
 * @author Makarius
 */

package isabelle.proofdocument


import java.util.regex.Pattern
import isabelle.prover.{Prover, Command}


case class StructureChange(
  val before_change: Command,
  val added_commands: List[Command],
  val removed_commands: List[Command])

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

class ProofDocument(text: Text, is_command_keyword: String => Boolean)
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

  private var first_token: Token = null
  private var last_token: Token = null
  
  private def tokens(start: Token, stop: Token) = new Iterator[Token] {
      var current = start
      def hasNext = current != stop && current != null
      def next() = { val save = current; current = current.next; save }
    }
  private def tokens(start: Token): Iterator[Token] = tokens(start, null)
  private def tokens(): Iterator[Token] = tokens(first_token, null)


  private def text_changed(start: Int, added_len: Int, removed_len: Int)
  {
    if (!active)
      return

    var before_change =
      if (Token.check_stop(first_token, _ < start)) Token.scan(first_token, _.stop >= start)
      else null
    
    var first_removed =
      if (before_change != null) before_change.next
      else if (Token.check_start(first_token, _ <= start + removed_len)) first_token
      else null 

    var last_removed = Token.scan(first_removed, _.start > start + removed_len)

    var shift_token =
      if (last_removed != null) last_removed
      else if (Token.check_start(first_token, _ > start)) first_token
      else null
    
    while (shift_token != null) {
      shift_token.shift(added_len - removed_len, start)
      shift_token = shift_token.next
    }
    
    // scan changed tokens until the end of the text or a matching token is
    // found which is beyond the changed area
    val match_start = if (before_change == null) 0 else before_change.stop
    var first_added: Token = null
    var last_added: Token = null

    val matcher = ProofDocument.token_pattern.matcher(text.content(match_start, text.length))
    var finished = false
    var position = 0 
    while (matcher.find(position) && !finished) {
      position = matcher.end
			val kind =
        if (is_command_keyword(matcher.group))
          Token.Kind.COMMAND_START
        else if (matcher.end - matcher.start > 2 && matcher.group.substring(0, 2) == "(*")
          Token.Kind.COMMENT
        else
          Token.Kind.OTHER
      val new_token = new Token(matcher.start + match_start, matcher.end + match_start, kind)

      if (first_added == null)
        first_added = new_token
      else {
        new_token.prev = last_added
        last_added.next = new_token
      }
      last_added = new_token
      
      while (Token.check_stop(last_removed, _ < new_token.stop) &&
              last_removed.next != null)
        last_removed = last_removed.next
			
      if (new_token.stop >= start + added_len &&
            Token.check_stop(last_removed, _ == new_token.stop))
        finished = true
    }

    var after_change = if (last_removed != null) last_removed.next else null
		
    // remove superflous first token-change
    if (first_added != null && first_added == first_removed &&
          first_added.stop < start) {
      before_change = first_removed
      if (last_removed == first_removed) {
        last_removed = null
        first_removed = null
      }
      else {
        first_removed = first_removed.next
        assert(first_removed != null)
      }

      if (last_added == first_added) {
        last_added = null
        first_added = null
      }
      if (first_added != null)
        first_added = first_added.next
    }
    
    // remove superflous last token-change
    if (last_added != null && last_added == last_removed &&
          last_added.start > start + added_len) {
      after_change = last_removed
      if (first_removed == last_removed) {
        first_removed = null
        last_removed = null
      }
      else {
        last_removed = last_removed.prev
        assert(last_removed != null)
      }
      
      if (last_added == first_added) {
        last_added = null
        first_added = null
      }
      else
        last_added = last_added.prev
    }
    
    if (first_removed == null && first_added == null)
      return
    
    if (first_token == null) {
      first_token = first_added
      last_token = last_added
    }
    else {
      // cut removed tokens out of list
      if (first_removed != null)
        first_removed.prev = null
      if (last_removed != null)
        last_removed.next = null
      
      if (first_token == first_removed)
        if (first_added != null)
          first_token = first_added
        else
          first_token = after_change
      
      if (last_token == last_removed)
        if (last_added != null)
          last_token = last_added
        else
          last_token = before_change
      
      // insert new tokens into list
      if (first_added != null) {
        first_added.prev = before_change
        if (before_change != null)
          before_change.next = first_added
        else
          first_token = first_added
      }
      else if (before_change != null)
        before_change.next = after_change
      
      if (last_added != null) {
        last_added.next = after_change
        if (after_change != null)
          after_change.prev = last_added
        else
          last_token = last_added
      }
      else if (after_change != null)
        after_change.prev = before_change
    }

    System.err.println("token_changed: " + before_change + " " + after_change + " " + first_removed)
    token_changed(before_change, after_change, first_removed)
  }
  

  
  /** command view **/

  val structural_changes = new EventBus[StructureChange]

  def commands = new Iterator[Command] {
    var current = first_token
    def hasNext = current != null
    def next() = { val s = current.command ; current = s.last.next ; s }
  }

  def find_command_at(pos: Int): Command = {
    for (cmd <- commands) { if (pos < cmd.stop) return cmd }
    return null
  }

  private def token_changed(start: Token, stop: Token, removed: Token)
  {
    var removed_commands: List[Command] = Nil
    var first: Command = null
    var last: Command = null

    for (t <- tokens(removed)) {
      if (first == null)
        first = t.command
      if (t.command != last)
        removed_commands = t.command :: removed_commands
      last = t.command
    }

    var before: Command = null
    if (!removed_commands.isEmpty) {
      if (first.first == removed) {
        if (start == null)
          before = null
        else
          before = start.command
      }
      else
        before = first.prev
    }

    var added_commands: List[Command] = Nil
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
          removed_commands = first :: removed_commands
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
      scan = first_token

    var stop_scan: Token = null
    if (stop != null) {
      if (stop == stop.command.first)
        stop_scan = stop
      else
        stop_scan = stop.command.last.next
    }
    else if (last != null)
      stop_scan = last.last.next
    else
      stop_scan = null

    var cmd_start: Token = null
    var cmd_stop: Token = null
    var overrun = false
    var finished = false
    while (scan != null && !finished) {
      if (scan == stop_scan) {
        if (scan.kind == Token.Kind.COMMAND_START)
          finished = true
        else
          overrun = true
      }

      if (scan.kind == Token.Kind.COMMAND_START && cmd_start != null && !finished) {
        if (!overrun) {
          added_commands = new Command(text, cmd_start, cmd_stop) :: added_commands
          cmd_start = scan
          cmd_stop = scan
        }
        else
          finished = true
      }
      else if (!finished) {
        if (cmd_start == null)
          cmd_start = scan
        cmd_stop = scan
      }
      if (overrun && !finished) {
        if (scan.command != last)
          removed_commands = scan.command :: removed_commands
        last = scan.command
      }

      if (!finished)
        scan = scan.next
    }

    if (cmd_start != null)
      added_commands = new Command(text, cmd_start, cmd_stop) :: added_commands

    // relink commands
    added_commands = added_commands.reverse
    removed_commands = removed_commands.reverse

    structural_changes.event(new StructureChange(before, added_commands, removed_commands))
  }
}
