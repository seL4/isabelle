/*  Title:      Pure/Thy/thy_syntax.scala
    Author:     Makarius

Superficial theory syntax: tokens and spans.
*/

package isabelle


import scala.collection.mutable
import scala.annotation.tailrec


object Thy_Syntax
{
  /** nested structure **/

  object Structure
  {
    sealed abstract class Entry { def length: Int }
    case class Block(val name: String, val body: List[Entry]) extends Entry
    {
      val length: Int = (0 /: body)(_ + _.length)
    }
    case class Atom(val command: Command) extends Entry
    {
      def length: Int = command.length
    }

    def parse(syntax: Outer_Syntax, node_name: Document.Node.Name, text: CharSequence): Entry =
    {
      /* stack operations */

      def buffer(): mutable.ListBuffer[Entry] = new mutable.ListBuffer[Entry]
      var stack: List[(Int, String, mutable.ListBuffer[Entry])] =
        List((0, "theory " + node_name.theory, buffer()))

      @tailrec def close(level: Int => Boolean)
      {
        stack match {
          case (lev, name, body) :: (_, _, body2) :: rest if level(lev) =>
            body2 += Block(name, body.toList)
            stack = stack.tail
            close(level)
          case _ =>
        }
      }

      def result(): Entry =
      {
        close(_ => true)
        val (_, name, body) = stack.head
        Block(name, body.toList)
      }

      def add(command: Command)
      {
        syntax.heading_level(command) match {
          case Some(i) =>
            close(_ >= i)
            stack = (i, command.source, buffer()) :: stack
          case None =>
        }
        stack.head._3 += Atom(command)
      }


      /* result structure */

      val spans = parse_spans(syntax.scan(text))
      spans.foreach(span => add(Command(node_name, span)))
      result()
    }
  }



  /** parse spans **/

  def parse_spans(toks: List[Token]): List[List[Token]] =
  {
    val result = new mutable.ListBuffer[List[Token]]
    val span = new mutable.ListBuffer[Token]

    def flush() { if (!span.isEmpty) { result += span.toList; span.clear } }
    for (tok <- toks) { if (tok.is_command) flush(); span += tok }
    flush()
    result.toList
  }



  /** perspective **/

  def command_perspective(node: Document.Node, perspective: Text.Perspective): Command.Perspective =
  {
    if (perspective.is_empty) Command.Perspective.empty
    else {
      val result = new mutable.ListBuffer[Command]
      @tailrec
      def check_ranges(ranges: List[Text.Range], commands: Stream[(Command, Text.Offset)])
      {
        (ranges, commands) match {
          case (range :: more_ranges, (command, offset) #:: more_commands) =>
            val command_range = command.range + offset
            range compare command_range match {
              case -1 => check_ranges(more_ranges, commands)
              case 0 =>
                result += command
                check_ranges(ranges, more_commands)
              case 1 => check_ranges(ranges, more_commands)
            }
          case _ =>
        }
      }
      check_ranges(perspective.ranges, node.command_range(perspective.range).toStream)
      Command.Perspective(result.toList)
    }
  }

  def update_perspective(nodes: Document.Nodes,
      name: Document.Node.Name, text_perspective: Text.Perspective)
    : (Command.Perspective, Option[Document.Nodes]) =
  {
    val node = nodes(name)
    val perspective = command_perspective(node, text_perspective)
    val new_nodes =
      if (node.perspective same perspective) None
      else Some(nodes + (name -> node.update_perspective(perspective)))
    (perspective, new_nodes)
  }

  def edit_perspective(previous: Document.Version,
      name: Document.Node.Name, text_perspective: Text.Perspective)
    : (Command.Perspective, Document.Version) =
  {
    val nodes = previous.nodes
    val (perspective, new_nodes) = update_perspective(nodes, name, text_perspective)
    val version = Document.Version.make(previous.syntax, new_nodes getOrElse nodes)
    (perspective, version)
  }



  /** text edits **/

  def text_edits(
      base_syntax: Outer_Syntax,
      previous: Document.Version,
      edits: List[Document.Edit_Text])
    : (List[Document.Edit_Command], Document.Version) =
  {
    /* phase 1: edit individual command source */

    @tailrec def edit_text(eds: List[Text.Edit], commands: Linear_Set[Command])
        : Linear_Set[Command] =
    {
      eds match {
        case e :: es =>
          Document.Node.command_starts(commands.iterator).find {
            case (cmd, cmd_start) =>
              e.can_edit(cmd.source, cmd_start) ||
                e.is_insert && e.start == cmd_start + cmd.length
          } match {
            case Some((cmd, cmd_start)) if e.can_edit(cmd.source, cmd_start) =>
              val (rest, text) = e.edit(cmd.source, cmd_start)
              val new_commands = commands.insert_after(Some(cmd), Command.unparsed(text)) - cmd
              edit_text(rest.toList ::: es, new_commands)

            case Some((cmd, cmd_start)) =>
              edit_text(es, commands.insert_after(Some(cmd), Command.unparsed(e.text)))

            case None =>
              require(e.is_insert && e.start == 0)
              edit_text(es, commands.insert_after(None, Command.unparsed(e.text)))
          }
        case Nil => commands
      }
    }


    /* phase 2: recover command spans */

    @tailrec def recover_spans(
      syntax: Outer_Syntax,
      node_name: Document.Node.Name,
      commands: Linear_Set[Command]): Linear_Set[Command] =
    {
      commands.iterator.find(cmd => !cmd.is_defined) match {
        case Some(first_unparsed) =>
          val first =
            commands.reverse_iterator(first_unparsed).
              dropWhile(_.newlines == 0).find(_.is_command) getOrElse commands.head
          val last =
            commands.iterator(first_unparsed).
              dropWhile(_.newlines == 0).find(_.is_command) getOrElse commands.last
          val range =
            commands.iterator(first).takeWhile(_ != last).toList ::: List(last)

          val sources = range.flatMap(_.span.map(_.source))
          val spans0 = parse_spans(syntax.scan(sources.mkString))

          val (before_edit, spans1) =
            if (!spans0.isEmpty && first.is_command && first.span == spans0.head)
              (Some(first), spans0.tail)
            else (commands.prev(first), spans0)

          val (after_edit, spans2) =
            if (!spans1.isEmpty && last.is_command && last.span == spans1.last)
              (Some(last), spans1.take(spans1.length - 1))
            else (commands.next(last), spans1)

          val inserted = spans2.map(span => Command(Document.new_id(), node_name, span))
          val new_commands =
            commands.delete_between(before_edit, after_edit).append_after(before_edit, inserted)
          recover_spans(syntax, node_name, new_commands)

        case None => commands
      }
    }


    /* resulting document edits */

    {
      val doc_edits = new mutable.ListBuffer[Document.Edit_Command]
      var nodes = previous.nodes
      var rebuild_syntax = previous.is_init

      // structure and syntax
      edits foreach {
        case (name, Document.Node.Header(header)) =>
          val node = nodes(name)
          val update_header =
            (node.header, header) match {
              case (Exn.Res(deps0), Exn.Res(deps)) => deps0 != deps
              case _ => true
            }
          if (update_header) {
            doc_edits += (name -> Document.Node.Header(header))
            val node1 = node.update_header(header)
            nodes += (name -> node1)
            rebuild_syntax = rebuild_syntax || (node.keywords != node1.keywords)
          }

        case _ =>
      }

      val syntax =
        if (rebuild_syntax)
          (base_syntax /: nodes.entries)({ case (syn, (_, node)) => (syn /: node.keywords)(_ + _) })
        else previous.syntax

      // node content
      edits foreach {  // FIXME observe rebuild_syntax!?
        case (name, Document.Node.Clear()) =>
          doc_edits += (name -> Document.Node.Clear())
          nodes += (name -> nodes(name).clear)

        case (name, Document.Node.Edits(text_edits)) =>
          val node = nodes(name)
          val commands0 = node.commands
          val commands1 = edit_text(text_edits, commands0)
          val commands2 = recover_spans(syntax, name, commands1)   // FIXME somewhat slow

          val removed_commands = commands0.iterator.filter(!commands2.contains(_)).toList
          val inserted_commands = commands2.iterator.filter(!commands0.contains(_)).toList

          val cmd_edits =
            removed_commands.reverse.map(cmd => (commands0.prev(cmd), None)) :::
            inserted_commands.map(cmd => (commands2.prev(cmd), Some(cmd)))

          doc_edits += (name -> Document.Node.Edits(cmd_edits))
          nodes += (name -> node.update_commands(commands2))

        case (name, Document.Node.Header(_)) =>

        case (name, Document.Node.Perspective(text_perspective)) =>
          update_perspective(nodes, name, text_perspective) match {
            case (_, None) =>
            case (perspective, Some(nodes1)) =>
              doc_edits += (name -> Document.Node.Perspective(perspective))
              nodes = nodes1
          }
      }
      (doc_edits.toList, Document.Version.make(syntax, nodes))
    }
  }
}
