/*
 * Document as list of commands, consisting of lists of tokens
 *
 * @author Johannes Hölzl, TU Munich
 * @author Fabian Immler, TU Munich
 * @author Makarius
 */

package isabelle.proofdocument


import scala.actors.Actor._

import java.util.regex.Pattern


object Proof_Document
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

  def empty(id: Isar_Document.Document_ID): Proof_Document =
    new Proof_Document(id, Linear_Set(), Map(), Linear_Set(), Map())

  type StructureChange = List[(Option[Command], Option[Command])]
}


class Proof_Document(
    val id: Isar_Document.Document_ID,
    val tokens: Linear_Set[Token],   // FIXME plain List, inside Command
    val token_start: Map[Token, Int],  // FIXME eliminate
    val commands: Linear_Set[Command],
    var states: Map[Command, Command])   // FIXME immutable, eliminate!?
  extends Session.Entity
{
  import Proof_Document.StructureChange

  def content = Token.string_from_tokens(Nil ++ tokens, token_start)


  /* accumulated messages */

  private val accumulator = actor {
    loop {
      react {
        case (session: Session, message: XML.Tree) =>
          message match {
            case XML.Elem(Markup.MESSAGE, (Markup.CLASS, Markup.STATUS) :: _, elems) =>
              for {
                XML.Elem(Markup.EDIT, (Markup.ID, cmd_id) :: (Markup.STATE, state_id) :: _, _)
                  <- elems
              } {
                session.lookup_entity(cmd_id) match {
                  case Some(cmd: Command) =>
                    val state = cmd.finish_static(state_id)
                    session.register_entity(state)
                    states += (cmd -> state)  // FIXME !?
                    session.command_change.event(cmd)   // FIXME really!?
                  case _ =>
                }
              }
            case _ =>
          }

        case bad => System.err.println("document accumulator: ignoring bad message " + bad)
      }
    }
  }

  def consume(session: Session, message: XML.Tree) { accumulator ! (session, message) }



  /** token view **/

  def text_changed(session: Session, change: Change): (Proof_Document, StructureChange) =
  {
    def edit_doc(doc_chgs: (Proof_Document, StructureChange), edit: Edit) = {
      val (doc, chgs) = doc_chgs
      val (new_doc, chg) = doc.text_edit(session, edit, change.id)
      (new_doc, chgs ++ chg)
    }
    ((this, Nil: StructureChange) /: change.edits)(edit_doc)
  }

  def text_edit(session: Session, e: Edit, id: String): (Proof_Document, StructureChange) =
  {
    case class TextChange(start: Int, added: String, removed: String)
    val change = e match {
      case Insert(s, a) => TextChange(s, a, "")
      case Remove(s, r) => TextChange(s, "", r)
    }
    //indices of tokens
    var start: Map[Token, Int] = token_start
    def stop(t: Token) = start(t) + t.length
    // split old token lists
    val tokens = Nil ++ this.tokens
    val (begin, remaining) = tokens.span(stop(_) < change.start)
    val (removed, end) = remaining.span(token_start(_) <= change.start + change.removed.length)
    // update indices
    start = end.foldLeft(start)((s, t) =>
      s + (t -> (s(t) + change.added.length - change.removed.length)))

    val split_begin = removed.takeWhile(start(_) < change.start).
      map (t => {
          val split_tok = new Token(t.content.substring(0, change.start - start(t)), t.kind)
          start += (split_tok -> start(t))
          split_tok
        })

    val split_end = removed.dropWhile(stop(_) < change.start + change.removed.length).
      map (t => {
          val split_tok =
            new Token(t.content.substring(change.start + change.removed.length - start(t)), t.kind)
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
      Proof_Document.token_pattern.matcher(Token.string_from_tokens(invalid_tokens, start))

    while (matcher.find() && invalid_tokens != Nil) {
			val kind =
        if (session.current_syntax.is_command(matcher.group))
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
          old_suffix = t :: ts
          new_tokens = new_tokens.tail
          invalid_tokens = Nil
        }
        case _ =>
      }
    }
    val insert = new_tokens.reverse
    val new_token_list = begin ::: insert ::: old_suffix
    token_changed(session, id, begin.lastOption, insert,
      old_suffix.firstOption, new_token_list, start)
  }


  /** command view **/

  private def token_changed(
    session: Session,
    new_id: String,
    before_change: Option[Token],
    inserted_tokens: List[Token],
    after_change: Option[Token],
    new_tokens: List[Token],
    new_token_start: Map[Token, Int]):
  (Proof_Document, StructureChange) =
  {
    val new_tokenset = Linear_Set[Token]() ++ new_tokens
    val cmd_before_change = before_change match {
      case None => None
      case Some(bc) =>
        val cmd_with_bc = commands.find(_.contains(bc)).get
        if (cmd_with_bc.tokens.last == bc) {
          if (new_tokenset.next(bc).map(_.is_start).getOrElse(true))
            Some(cmd_with_bc)
          else commands.prev(cmd_with_bc)
        }
        else commands.prev(cmd_with_bc)
    }

    val cmd_after_change = after_change match {
      case None => None
      case Some(ac) =>
        val cmd_with_ac = commands.find(_.contains(ac)).get
        if (ac.is_start)
          Some(cmd_with_ac)
        else
          commands.next(cmd_with_ac)
    }

    val removed_commands = commands.dropWhile(Some(_) != cmd_before_change).drop(1).
      takeWhile(Some(_) != cmd_after_change)

    // calculate inserted commands
    def tokens_to_commands(tokens: List[Token]): List[Command]= {
      tokens match {
        case Nil => Nil
        case t :: ts =>
          val (cmd, rest) =
            ts.span(t => t.kind != Token.Kind.COMMAND_START && t.kind != Token.Kind.COMMENT)
          new Command(session.create_id(), t :: cmd, new_token_start) :: tokens_to_commands(rest)
      }
    }

    val split_begin =
      if (before_change.isDefined) {
        val changed =
          if (cmd_before_change.isDefined)
            new_tokens.dropWhile(_ != cmd_before_change.get.tokens.last).drop(1)
          else new_tokenset
        if (changed.exists(_ == before_change.get))
          changed.takeWhile(_ != before_change.get).toList :::
            List(before_change.get)
        else Nil
      } else Nil

    val split_end =
      if (after_change.isDefined) {
        val unchanged = new_tokens.dropWhile(_ != after_change.get)
        if(cmd_after_change.isDefined) {
          if (unchanged.exists(_ == cmd_after_change.get.tokens.first))
            unchanged.takeWhile(_ != cmd_after_change.get.tokens.first).toList
          else Nil
        } else {
          unchanged
        }
      } else Nil

    val rescan_begin =
      split_begin :::
        before_change.map(bc => new_tokens.dropWhile(_ != bc).drop(1)).getOrElse(new_tokens)
    val rescanning_tokens =
      after_change.map(ac => rescan_begin.takeWhile(_ != ac)).getOrElse(rescan_begin) :::
        split_end
    val inserted_commands = tokens_to_commands(rescanning_tokens.toList)

    // build new document
    val new_commandset = commands.
      delete_between(cmd_before_change, cmd_after_change).
      append_after(cmd_before_change, inserted_commands)


    val doc =
      new Proof_Document(new_id, new_tokenset, new_token_start, new_commandset,
        states -- removed_commands)

    val removes =
      for (cmd <- removed_commands) yield (cmd_before_change -> None)
    val inserts =
      for (cmd <- inserted_commands) yield (doc.commands.prev(cmd) -> Some(cmd))

    return (doc, removes.toList ++ inserts)
  }

  val commands_offsets = {
    var last_stop = 0
    (for (c <- commands) yield {
      val r = c -> (last_stop,c.stop(this))
      last_stop = c.stop(this)
      r
    }).toArray
  }

  def command_at(pos: Int): Option[Command] =
    find_command(pos, 0, commands_offsets.length)

  // use a binary search to find commands for a given offset
  private def find_command(pos: Int, array_start: Int, array_stop: Int): Option[Command] =
  {
    val middle_index = (array_start + array_stop) / 2
    if (middle_index >= commands_offsets.length) return None
    val (middle, (start, stop)) = commands_offsets(middle_index)
    // does middle contain pos?
    if (start <= pos && pos < stop)
      Some(middle)
    else if (start > pos)
      find_command(pos, array_start, middle_index)
    else if (stop <= pos)
      find_command(pos, middle_index + 1, array_stop)
    else error("impossible")
  }
}
