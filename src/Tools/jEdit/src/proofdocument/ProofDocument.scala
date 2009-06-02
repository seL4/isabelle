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
  // Be careful when changing this regex. Not only must it handle the
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
  new ProofDocument(isabelle.jedit.Isabelle.plugin.id(),
    LinearSet(), Map(), LinearSet(), false, _ => false)

}

class ProofDocument(
  val id: String,
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

  def content = Token.string_from_tokens(Nil ++ tokens, token_start)
  /** token view **/

  def text_changed(change: Text.Change): (ProofDocument, StructureChange) =
  {
    //indices of tokens
    var start: Map[Token, Int] = token_start
    def stop(t: Token) = start(t) + t.length
    // split old token lists
    val tokens = Nil ++ this.tokens
    val (begin, remaining) = tokens.span(stop(_) < change.start)
    val (removed, end) = remaining.span(token_start(_) <= change.start + change.removed)
    // update indices
    start = end.foldLeft(start)((s, t) =>
      s + (t -> (s(t) + change.added.length - change.removed)))

    val split_begin = removed.takeWhile(start(_) < change.start).
      map (t => {
          val split_tok = new Token(t.content.substring(0, change.start - start(t)), t.kind)
          start += (split_tok -> start(t))
          split_tok
        })

    val split_end = removed.dropWhile(stop(_) < change.start + change.removed).
      map (t => {
          val split_tok =
            new Token(t.content.substring(change.start + change.removed - start(t)), t.kind)
          start += (split_tok -> start(t))
          split_tok
        })
    // update indices
    start = removed.foldLeft (start) ((s, t) => s - t)
    start = split_end.foldLeft (start) ((s, t) =>
    s + (t -> (change.start + change.added.length)))

    val ins = new Token(change.added, Token.Kind.OTHER)
    start += (ins -> change.start)
    
    var invalid_tokens = split_begin ::: ins :: split_end ::: end
    var new_tokens: List[Token] = Nil
    var old_suffix: List[Token] = Nil

    val match_start = invalid_tokens.firstOption.map(start(_)).getOrElse(0)
    val matcher =
      ProofDocument.token_pattern.matcher(Token.string_from_tokens(invalid_tokens, start))

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
        case t :: ts =>
          if (start(t) == start(new_token) &&
              start(t) > change.start + change.added.length) {
          old_suffix = ts
          invalid_tokens = Nil
        }
        case _ =>
      }
    }
    val insert = new_tokens.reverse
    val new_token_list = begin ::: insert ::: old_suffix
    val new_tokenset = (LinearSet() ++ new_token_list).asInstanceOf[LinearSet[Token]]
    token_changed(change.id, begin.lastOption, insert,
      old_suffix.firstOption, new_tokenset, start)
  }

  
  /** command view **/

  def find_command_at(pos: Int): Command = {
    for (cmd <- commands) { if (pos < cmd.stop(this)) return cmd }
    return null
  }

  private def token_changed(
    new_id: String,
    before_change: Option[Token],
    inserted_tokens: List[Token],
    after_change: Option[Token],
    new_tokenset: LinearSet[Token],
    new_token_start: Map[Token, Int]): (ProofDocument, StructureChange) =
  {
    val cmd_first_changed =
      if (before_change.isDefined) commands.find(_.tokens.contains(before_change.get))
      else None
    val cmd_last_changed =
      if (after_change.isDefined) commands.find(_.tokens.contains(after_change.get))
      else None

    val cmd_before_change =
      if (cmd_first_changed.isDefined) commands.prev(cmd_first_changed.get)
      else None
    val cmd_after_change =
      if (cmd_last_changed.isDefined) commands.next(cmd_last_changed.get)
      else None

    val removed_commands = commands.dropWhile(Some(_) != cmd_first_changed).
      takeWhile(Some(_) != cmd_after_change)

    // calculate inserted commands
    def tokens_to_commands(tokens: List[Token]): List[Command]= {
      tokens match {
        case Nil => Nil
        case t :: ts =>
          val (cmd, rest) =
            ts.span(t => t.kind != Token.Kind.COMMAND_START && t.kind != Token.Kind.COMMENT)
          new Command(t :: cmd, new_token_start) :: tokens_to_commands(rest)
      }
    }

    val split_begin_tokens =
      if (!cmd_first_changed.isDefined || !before_change.isDefined) Nil
      else {
        cmd_first_changed.get.tokens.takeWhile(_ != before_change.get) :::
          List(before_change.get)
      }
    val split_end_tokens =
      if (!cmd_last_changed.isDefined || !after_change.isDefined) Nil
      else {
        cmd_last_changed.get.tokens.dropWhile(_ != after_change.get)
      }

    val rescanning_tokens =
      split_begin_tokens ::: inserted_tokens ::: split_end_tokens
    val inserted_commands = tokens_to_commands(rescanning_tokens)

    val change = new StructureChange(cmd_before_change, inserted_commands, removed_commands.toList)
    // build new document
    val new_commandset = commands.delete_between(cmd_before_change, cmd_after_change).
        insert_after(cmd_before_change, inserted_commands)

    val doc =
      new ProofDocument(new_id, new_tokenset, new_token_start,
        new_commandset, active, is_command_keyword)
    return (doc, change)
  }
}
