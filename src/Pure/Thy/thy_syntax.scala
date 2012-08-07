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
            close(_ > i)
            stack = (i + 1, command.source, buffer()) :: stack
          case None =>
        }
        stack.head._3 += Atom(command)
      }


      /* result structure */

      val spans = parse_spans(syntax.scan(text))
      spans.foreach(span => add(Command(Document.no_id, node_name, span)))
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



  /** header edits: structure and outer syntax **/

  private def header_edits(
    base_syntax: Outer_Syntax,
    previous: Document.Version,
    edits: List[Document.Edit_Text])
    : (Outer_Syntax, List[Document.Node.Name], Document.Nodes, List[Document.Edit_Command]) =
  {
    var updated_imports = false
    var updated_keywords = false
    var nodes = previous.nodes
    val doc_edits = new mutable.ListBuffer[Document.Edit_Command]

    edits foreach {
      case (name, Document.Node.Header(header)) =>
        val node = nodes(name)
        val update_header =
          (node.header, header) match {
            case (Exn.Res(deps0), Exn.Res(deps)) => deps0 != deps
            case _ => true
          }
        if (update_header) {
          val node1 = node.update_header(header)
          updated_imports = updated_imports || (node.imports != node1.imports)
          updated_keywords = updated_keywords || (node.keywords != node1.keywords)
          nodes += (name -> node1)
          doc_edits += (name -> Document.Node.Header(header))
        }
      case _ =>
    }

    val syntax =
      if (previous.is_init || updated_keywords)
        (base_syntax /: nodes.entries) { case (syn, (_, node)) => syn.add_keywords(node.header) }
      else previous.syntax

    val reparse =
      if (updated_imports || updated_keywords)
        nodes.descendants(doc_edits.iterator.map(_._1).toList)
      else Nil

    (syntax, reparse, nodes, doc_edits.toList)
  }



  /** text edits **/

  /* phase 1: edit individual command source */

  @tailrec private def edit_text(eds: List[Text.Edit], commands: Linear_Set[Command])
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

  @tailrec private def recover_spans(
    syntax: Outer_Syntax,
    node_name: Document.Node.Name,
    commands: Linear_Set[Command]): Linear_Set[Command] =
  {
    commands.iterator.find(cmd => !cmd.is_defined) match {
      case Some(first_undefined) =>
        val first =
          commands.reverse_iterator(first_undefined).
            dropWhile(_.newlines == 0).find(_.is_command) getOrElse commands.head
        val last =
          commands.iterator(first_undefined).
            dropWhile(_.newlines == 0).find(_.is_command) getOrElse commands.last
        val range =
          commands.iterator(first).takeWhile(_ != last).toList ::: List(last)

        val spans0 = parse_spans(syntax.scan(range.map(_.source).mkString))

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


  /* phase 3: full reparsing after syntax change */

  private def reparse_spans(
    syntax: Outer_Syntax,
    node_name: Document.Node.Name,
    commands: Linear_Set[Command]): Linear_Set[Command] =
  {
    val cmds = commands.toList
    val spans1 = parse_spans(syntax.scan(cmds.map(_.source).mkString))
    if (cmds.map(_.span) == spans1) commands
    else Linear_Set(spans1.map(span => Command(Document.new_id(), node_name, span)): _*)
  }


  /* main phase */

  def text_edits(
      base_syntax: Outer_Syntax,
      previous: Document.Version,
      edits: List[Document.Edit_Text])
    : (List[Document.Edit_Command], Document.Version) =
  {
    val (syntax, reparse, nodes0, doc_edits0) = header_edits(base_syntax, previous, edits)
    val reparse_set = reparse.toSet

    var nodes = nodes0
    val doc_edits = new mutable.ListBuffer[Document.Edit_Command]; doc_edits ++= doc_edits0

    (edits ::: reparse.map((_, Document.Node.Edits(Nil)))) foreach {
      case (name, Document.Node.Clear()) =>
        doc_edits += (name -> Document.Node.Clear())
        nodes += (name -> nodes(name).clear)

      case (name, Document.Node.Edits(text_edits)) =>
        val node = nodes(name)
        val commands0 = node.commands
        val commands1 = edit_text(text_edits, commands0)
        val commands2 = recover_spans(syntax, name, commands1)   // FIXME somewhat slow
        val commands3 =
          if (reparse_set.contains(name)) reparse_spans(syntax, name, commands2)  // slow
          else commands2

        val removed_commands = commands0.iterator.filter(!commands3.contains(_)).toList
        val inserted_commands = commands3.iterator.filter(!commands0.contains(_)).toList

        val cmd_edits =
          removed_commands.reverse.map(cmd => (commands0.prev(cmd), None)) :::
          inserted_commands.map(cmd => (commands3.prev(cmd), Some(cmd)))

        doc_edits += (name -> Document.Node.Edits(cmd_edits))
        nodes += (name -> node.update_commands(commands3))

      case (name, Document.Node.Header(_)) =>

      case (name, Document.Node.Perspective(text_perspective)) =>
        val node = nodes(name)
        val perspective = command_perspective(node, text_perspective)
        if (!(node.perspective same perspective)) {
          doc_edits += (name -> Document.Node.Perspective(perspective))
          nodes += (name -> node.update_perspective(perspective))
        }
    }
    (doc_edits.toList, Document.Version.make(syntax, nodes))
  }
}
