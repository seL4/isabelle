/*
 * Document as list of tokens
 *
 * @author Johannes Hölzl, TU Munich
 */

package isabelle.proofdocument


import java.util.regex.Pattern


object ProofDocument
{
  // Be carefully when changeing this regex. Not only must it handle the 
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

abstract class ProofDocument(text: Text)
{
  protected var firstToken: Token = null
  protected var lastToken: Token = null
  private var active = false 
  
  text.changes += (e => textChanged(e.start, e.added, e.removed))
	
  def activate() {
    if (!active) {
      active = true
      textChanged(0, text.length, 0)
    }
  }
  
  protected def tokens(start: Token, stop: Token) =
    new Iterator[Token] {
      var current = start
      def hasNext = current != stop && current != null
      def next() = { val save = current ; current = current.next ; save }
    }
  
  protected def tokens(start: Token): Iterator[Token] = 
    tokens(start, null)
  
  protected def tokens() : Iterator[Token] =
    tokens(firstToken, null)

  private def textChanged(start : Int, addedLen : Int, removedLen : Int) {
    val check_start = Token.check_start _
    val check_stop = Token.check_stop _
    val scan = Token.scan _
    if (active == false)
      return
        
    var beforeChange = 
      if (check_stop(firstToken, _ < start)) scan(firstToken, _.stop >= start)
      else null
    
    var firstRemoved = 
      if (beforeChange != null) beforeChange.next
      else if (check_start(firstToken, _ <= start + removedLen)) firstToken
      else null 

    var lastRemoved = scan(firstRemoved, _.start > start + removedLen)

    var shiftToken = 
      if (lastRemoved != null) lastRemoved
      else if (check_start(firstToken, _ > start)) firstToken
      else null
    
    while(shiftToken != null) {
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
			val kind = if(isStartKeyword(matcher.group())) {
        Token.Kind.COMMAND_START
      } else if (matcher.end() - matcher.start() > 2 && matcher.group().substring(0, 2) == "(*") {
        Token.Kind.COMMENT
      } else {
        Token.Kind.OTHER
      }
      val newToken = new Token(matcher.start() + matchStart, matcher.end() + matchStart, kind)

      if (firstAdded == null)
        firstAdded = newToken
      else {
        newToken.prev = lastAdded
        lastAdded.next = newToken
      }
      lastAdded = newToken
      
      while (check_stop(lastRemoved, _ < newToken.stop) &&
              lastRemoved.next != null)	
        lastRemoved = lastRemoved.next
			
      if (newToken.stop >= start + addedLen && 
            check_stop(lastRemoved, _ == newToken.stop))
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
        if (firstRemoved == null)
          System.err.println("ERROR")
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
        if (lastRemoved == null)
          System.err.println("ERROR")
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
    
    tokenChanged(beforeChange, afterChange, firstRemoved)
  }
  
  protected def isStartKeyword(str: String): Boolean
  
  protected def tokenChanged(start: Token, stop: Token, removed: Token) 
}
