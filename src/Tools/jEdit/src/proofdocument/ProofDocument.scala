/*
 * Document as list of commands, consisting of lists of tokens
 *
 * @author Johannes Hölzl, TU Munich
 * @author Fabian Immler, TU Munich
 * @author Makarius
 */

package isabelle.proofdocument

import scala.collection.mutable.ListBuffer
import scala.actors.Actor
import scala.actors.Actor._
import java.util.regex.Pattern
import isabelle.prover.{Prover, Command}
import isabelle.utils.LinearSet

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

 val empty =
  new ProofDocument(isabelle.jedit.Isabelle.plugin.id(), LinearSet(), Map(), LinearSet(), false, _ => false)

}

class ProofDocument(val id: String,
                    val tokens: LinearSet[Token],
                    val token_start: Map[Token, Int],
                    val commands: LinearSet[Command],
                    val active: Boolean,
                    is_command_keyword: String => Boolean)
{

  def mark_active: ProofDocument =
    new ProofDocument(id, tokens, token_start, commands, true, is_command_keyword)
  def activate: (ProofDocument, StructureChange) = {
    val (doc, change) =
      text_changed(new Text.Change(isabelle.jedit.Isabelle.plugin.id(), 0, content, content.length))
    return (doc.mark_active, change)
  }
  def set_command_keyword(f: String => Boolean): ProofDocument =
    new ProofDocument(id, tokens, token_start, commands, active, f)

  def content = Token.string_from_tokens(List() ++ tokens, token_start)
  /** token view **/

  def text_changed(change: Text.Change): (ProofDocument, StructureChange) =
  {
    //indices of tokens
    var start: Map[Token, Int] = token_start
    def stop(t: Token) = start(t) + t.length
    // split old token lists
    val tokens = List() ++ this.tokens
    val (begin, remaining) = tokens.span(stop(_) < change.start)
    val (removed, end) = remaining.span(token_start(_) <= change.start + change.removed)
    // update indices
    start = end.foldLeft (start) ((s, t) => s + (t -> (s(t) + change.added.length - change.removed)))
    start = removed.foldLeft (start) ((s, t) => s - t)

    val split_begin = removed.takeWhile(start(_) < change.start).
      map (t => new Token(t.content.substring(0, change.start - start(t)),
                          t.kind))
    val split_end = removed.dropWhile(stop(_) < change.start + change.removed).
      map (t => new Token(t.content.substring(change.start + change.removed - start(t)),
                          t.kind))
    // update indices
    start = split_end.foldLeft (start) ((s, t) => s + (t -> (change.start + change.added.length)))

    val ins = new Token(change.added, Token.Kind.OTHER)
    start += (ins -> change.start)
    
    var invalid_tokens =  split_begin :::
       ins :: split_end ::: end
    var new_tokens = Nil: List[Token]
    var old_suffix = Nil: List[Token]

    val match_start = invalid_tokens.firstOption.map(start(_)).getOrElse(0)
    val matcher = ProofDocument.token_pattern.matcher(Token.string_from_tokens(invalid_tokens, start))

    while (matcher.find() && invalid_tokens != Nil) {
			val kind =
        if (is_command_keyword(matcher.group))
          Token.Kind.COMMAND_START
        else if (matcher.end - matcher.start > 2 && matcher.group.substring(0, 2) == "(*")
          Token.Kind.COMMENT
        else
          Token.Kind.OTHER
      val new_token = new Token(matcher.group, kind)
      start += (new_token -> (match_start + matcher.start))
      new_tokens ::= new_token

      invalid_tokens = invalid_tokens dropWhile (stop(_) < stop(new_token))
      invalid_tokens match {
        case t::ts => if(start(t) == start(new_token) &&
                         start(t) > change.start + change.added.length) {
          old_suffix = ts
          invalid_tokens = Nil
        }
        case _ =>
      }
    }
    val insert = new_tokens.reverse
    val new_token_list = begin ::: insert ::: old_suffix
    token_changed(change.id,
                  begin.lastOption,
                  insert,
                  removed,
                  old_suffix.firstOption,
                  new_token_list,
                  start)
  }
  
  /** command view **/

  def find_command_at(pos: Int): Command = {
    for (cmd <- commands) { if (pos < cmd.stop) return cmd }
    return null
  }

  private def token_changed(new_id: String,
                            before_change: Option[Token],
                            inserted_tokens: List[Token],
                            removed_tokens: List[Token],
                            after_change: Option[Token],
                            new_token_list: List[Token],
                            new_token_start: Map[Token, Int]): (ProofDocument, StructureChange) =
  {
    val commands_list = List[Command]() ++ commands

    // calculate removed commands
    val first_removed = removed_tokens.firstOption

    val (begin, remaining) =
      first_removed match {
        case None => (Nil, commands_list)
        case Some(fr) => commands_list.break(_.tokens.contains(fr))
      }
    val (removed_commands, end) =
      after_change match {
        case None => (remaining, Nil)
        case Some(ac) => remaining.break(_.tokens.contains(ac))
      }

    def tokens_to_commands(tokens: List[Token]): List[Command]= {
      tokens match {
        case Nil => Nil
        case t::ts =>
          val (cmd,rest) = ts.span(_.kind != Token.Kind.COMMAND_START)
          new Command(t::cmd) :: tokens_to_commands (rest)
      }
    }

    // calculate inserted commands
    val new_commands = tokens_to_commands(new_token_list)
    val new_tokenset = (LinearSet() ++ new_token_list).asInstanceOf[LinearSet[Token]]
    val new_commandset = (LinearSet() ++ (new_commands)).asInstanceOf[LinearSet[Command]]
    // drop known commands from the beginning
    val first_changed = before_change match {
      case None => new_tokenset.first_elem
      case Some(bc) => new_tokenset.next(bc)
    }
    val changed_commands = first_changed match {
      case None => Nil
      case Some(fc) => new_commands.dropWhile(!_.tokens.contains(fc))
    }
    val inserted_commands = after_change match {
      case None => changed_commands
      case Some(ac) => changed_commands.takeWhile(!_.tokens.contains(ac))
    }
    val change = new StructureChange(new_commands.find(_.tokens.contains(before_change)),
                                     inserted_commands, removed_commands)
    // build new document
    var new_commands = commands
    while(new_commands.next())
    val doc =
      new ProofDocument(new_id, new_tokenset, new_token_start, new_commandset, active, is_command_keyword)
    return (doc, change)
  }
}
