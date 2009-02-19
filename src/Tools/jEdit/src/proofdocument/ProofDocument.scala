/*
 * Document as list of commands, consisting of lists of tokens
 *
 * @author Johannes Hölzl, TU Munich
 * @author Makarius
 */

package isabelle.proofdocument

import scala.collection.mutable.ListBuffer
import java.util.regex.Pattern
import isabelle.prover.{Prover, Command}


case class StructureChange(
  val before_change: Option[Command],
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
      text_changed(new Text.Change(0, content, content.length))
    }
  }

  text.changes += (change => text_changed(change))

  var tokens = Nil : List[Token]
  var commands = Nil : List[Command]
  def content = Token.string_from_tokens(tokens)
  /** token view **/

  private def text_changed(change: Text.Change)
  {
    val (begin, remaining) = tokens.span(_.stop < change.start)
    val (removed, end) = remaining.span(_.start <= change.start + change.removed)
    for (t <- end) t.start += (change.added.length - change.removed)

    val split_begin = removed.takeWhile(_.start < change.start).
      map (t => new Token(t.start,
                          t.content.substring(0, change.start - t.start),
                          t.kind))
    val split_end = removed.dropWhile(_.stop < change.start + change.removed).
      map (t => new Token(change.start + change.added.length,
                          t.content.substring(change.start + change.removed - t.start),
                          t.kind))

    var invalid_tokens =  split_begin :::
      new Token(change.start, change.added, Token.Kind.OTHER) :: split_end ::: end
    var new_tokens = Nil: List[Token]
    var old_suffix = Nil: List[Token]

    val match_start = invalid_tokens.first.start
    val matcher = ProofDocument.token_pattern.matcher(Token.string_from_tokens(invalid_tokens))

    while (matcher.find() && invalid_tokens != Nil) {
			val kind =
        if (is_command_keyword(matcher.group))
          Token.Kind.COMMAND_START
        else if (matcher.end - matcher.start > 2 && matcher.group.substring(0, 2) == "(*")
          Token.Kind.COMMENT
        else
          Token.Kind.OTHER
      val new_token = new Token(match_start + matcher.start, matcher.group, kind)
      new_tokens ::= new_token

      invalid_tokens = invalid_tokens dropWhile (_.stop < new_token.stop)
      invalid_tokens match {
        case t::ts => if(t.start == new_token.start &&
                         t.start > change.start + change.added.length) {
          old_suffix = ts
          invalid_tokens = Nil
        }
        case _ =>
      }
    }
    val insert = new_tokens.reverse
    tokens = begin ::: insert ::: old_suffix

    token_changed(begin.lastOption,
                  insert,
                  removed,
                  old_suffix.firstOption)
  }
  
  /** command view **/

  val structural_changes = new EventBus[StructureChange]

  def find_command_at(pos: Int): Command = {
    for (cmd <- commands) { if (pos < cmd.stop) return cmd }
    return null
  }

  private def token_changed(before_change: Option[Token],
                            inserted_tokens: List[Token],
                            removed_tokens: List[Token],
                            after_change: Option[Token])
  {
    val (begin, remaining) =
      before_change match {
        case None => (Nil, commands)
        case Some(bc) => commands.break(_.tokens.contains(bc))
      }
    val (_removed, _end) =
      after_change match {
        case None => (remaining, Nil)
        case Some(ac) => remaining.break(_.tokens.contains(ac))
      }
    val (removed, end) = _end match {
      case Nil => (_removed, Nil)
      case acc::end => if (after_change.isDefined && after_change.get.kind == Token.Kind.COMMAND_START)
          (_removed, _end)
        else (_removed ::: List(acc), end)
    }
    val all_removed_tokens = for(c <- removed; t <- c.tokens) yield t
    val (pseudo_new_pre, rest) =
      if (! before_change.isDefined) (Nil, all_removed_tokens)
      else {
        val (a, b) = all_removed_tokens.span (_ != before_change.get)
        b match {
          case Nil => (a, Nil)
          case bc::rest => (a ::: List(bc), b)
        }
      }
    val pseudo_new_post = rest.dropWhile(Some(_) != after_change)

    def tokens_to_commands(tokens: List[Token]): List[Command]= {
      tokens match {
        case Nil => Nil
        case t::ts =>
          val (cmd,rest) = ts.span(_.kind != Token.Kind.COMMAND_START)
          new Command(t::cmd) :: tokens_to_commands (rest)
      }
    }

    System.err.println("ins_tokens: " + inserted_tokens)
    val new_commands = tokens_to_commands(pseudo_new_pre ::: inserted_tokens ::: pseudo_new_post)
    System.err.println("new_commands: " + new_commands)

    commands = begin ::: new_commands ::: end
    val before = begin match {case Nil => None case _ => Some (begin.last)}
    structural_changes.event(new StructureChange(before, new_commands, removed))
/*
    val old = commands
    commands = tokens_to_commands(tokens)
    structural_changes.event(new StructureChange(None, commands, old)) */
  }
}
