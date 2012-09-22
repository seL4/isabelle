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
        List((0, node_name.theory, buffer()))

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
      spans.foreach(span => add(Command(Document.no_id, node_name, span, Markup_Tree.empty)))
      result()
    }
  }



  /** parse spans **/

  def parse_spans(toks: List[Token]): List[Command.Span] =
  {
    val result = new mutable.ListBuffer[Command.Span]
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
      case (name, Document.Node.Deps(header)) =>
        val node = nodes(name)
        val update_header =
          !node.header.errors.isEmpty || !header.errors.isEmpty || node.header != header
        if (update_header) {
          val node1 = node.update_header(header)
          updated_imports = updated_imports || (node.header.imports != node1.header.imports)
          updated_keywords = updated_keywords || (node.header.keywords != node1.header.keywords)
          nodes += (name -> node1)
          doc_edits += (name -> Document.Node.Deps(header))
        }
      case _ =>
    }

    val syntax =
      if (previous.is_init || updated_keywords)
        (base_syntax /: nodes.entries) {
          case (syn, (_, node)) => syn.add_keywords(node.header.keywords)
        }
      else previous.syntax

    val reparse =
      if (updated_imports || updated_keywords)
        nodes.descendants(doc_edits.iterator.map(_._1).toList)
      else Nil

    (syntax, reparse, nodes, doc_edits.toList)
  }



  /** text edits **/

  /* edit individual command source */

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


  /* reparse range of command spans */

  @tailrec private def chop_common(
      cmds: List[Command], spans: List[Command.Span]): (List[Command], List[Command.Span]) =
    (cmds, spans) match {
      case (c :: cs, s :: ss) if c.span == s => chop_common(cs, ss)
      case _ => (cmds, spans)
    }

  private def reparse_spans(
    syntax: Outer_Syntax,
    name: Document.Node.Name,
    commands: Linear_Set[Command],
    first: Command, last: Command): Linear_Set[Command] =
  {
    val cmds0 = commands.iterator(first, last).toList
    val spans0 = parse_spans(syntax.scan(cmds0.iterator.map(_.source).mkString))

    val (cmds1, spans1) = chop_common(cmds0, spans0)

    val (rev_cmds2, rev_spans2) = chop_common(cmds1.reverse, spans1.reverse)
    val cmds2 = rev_cmds2.reverse
    val spans2 = rev_spans2.reverse

    cmds2 match {
      case Nil =>
        assert(spans2.isEmpty)
        commands
      case cmd :: _ =>
        val hook = commands.prev(cmd)
        val inserted = spans2.map(span => Command(Document.new_id(), name, span, Markup_Tree.empty))
        (commands /: cmds2)(_ - _).append_after(hook, inserted)
    }
  }


  /* recover command spans after edits */

  // FIXME somewhat slow
  private def recover_spans(
    syntax: Outer_Syntax,
    name: Document.Node.Name,
    perspective: Command.Perspective,
    commands: Linear_Set[Command]): Linear_Set[Command] =
  {
    val visible = perspective.commands.toSet

    def next_invisible_command(cmds: Linear_Set[Command], from: Command): Command =
      cmds.iterator(from).dropWhile(cmd => !cmd.is_command || visible(cmd))
        .find(_.is_command) getOrElse cmds.last

    @tailrec def recover(cmds: Linear_Set[Command]): Linear_Set[Command] =
      cmds.find(_.is_unparsed) match {
        case Some(first_unparsed) =>
          val first = next_invisible_command(cmds.reverse, first_unparsed)
          val last = next_invisible_command(cmds, first_unparsed)
          recover(reparse_spans(syntax, name, cmds, first, last))
        case None => cmds
      }
    recover(commands)
  }


  /* consolidate unfinished spans */

  private def consolidate_spans(
    syntax: Outer_Syntax,
    reparse_limit: Int,
    name: Document.Node.Name,
    perspective: Command.Perspective,
    commands: Linear_Set[Command]): Linear_Set[Command] =
  {
    if (perspective.commands.isEmpty) commands
    else {
      commands.find(_.is_unfinished) match {
        case Some(first_unfinished) =>
          val visible = perspective.commands.toSet
          commands.reverse.find(visible) match {
            case Some(last_visible) =>
              val it = commands.iterator(last_visible)
              var last = last_visible
              var i = 0
              while (i < reparse_limit && it.hasNext) {
                last = it.next
                i += last.length
              }
              reparse_spans(syntax, name, commands, first_unfinished, last)
            case None => commands
          }
        case None => commands
      }
    }
  }


  /* main */

  private def diff_commands(old_cmds: Linear_Set[Command], new_cmds: Linear_Set[Command])
    : List[(Option[Command], Option[Command])] =
  {
    val removed = old_cmds.iterator.filter(!new_cmds.contains(_)).toList
    val inserted = new_cmds.iterator.filter(!old_cmds.contains(_)).toList

    removed.reverse.map(cmd => (old_cmds.prev(cmd), None)) :::
    inserted.map(cmd => (new_cmds.prev(cmd), Some(cmd)))
  }

  private def text_edit(syntax: Outer_Syntax, reparse_limit: Int,
    node: Document.Node, edit: Document.Edit_Text): Document.Node =
  {
    edit match {
      case (_, Document.Node.Clear()) => node.clear

      case (name, Document.Node.Edits(text_edits)) =>
        val commands0 = node.commands
        val commands1 = edit_text(text_edits, commands0)
        val commands2 = recover_spans(syntax, name, node.perspective, commands1)
        node.update_commands(commands2)

      case (_, Document.Node.Deps(_)) => node

      case (name, Document.Node.Perspective(text_perspective)) =>
        val perspective = command_perspective(node, text_perspective)
        if (node.perspective same perspective) node
        else
          node.update_perspective(perspective).update_commands(
            consolidate_spans(syntax, reparse_limit, name, perspective, node.commands))
    }
  }

  def text_edits(
      base_syntax: Outer_Syntax,
      reparse_limit: Int,
      previous: Document.Version,
      edits: List[Document.Edit_Text])
    : (List[Document.Edit_Command], Document.Version) =
  {
    val (syntax, reparse, nodes0, doc_edits0) = header_edits(base_syntax, previous, edits)
    val reparse_set = reparse.toSet

    var nodes = nodes0
    val doc_edits = new mutable.ListBuffer[Document.Edit_Command]; doc_edits ++= doc_edits0

    val node_edits =
      (edits ::: reparse.map((_, Document.Node.Edits(Nil)))).groupBy(_._1)
        .asInstanceOf[Map[Document.Node.Name, List[Document.Edit_Text]]]  // FIXME ???

    node_edits foreach {
      case (name, edits) =>
        val node = nodes(name)
        val commands = node.commands

        val node1 =
          if (reparse_set(name) && !commands.isEmpty)
            node.update_commands(reparse_spans(syntax, name, commands, commands.head, commands.last))
          else node
        val node2 = (node1 /: edits)(text_edit(syntax, reparse_limit, _, _))

        if (!(node.perspective same node2.perspective))
          doc_edits += (name -> Document.Node.Perspective(node2.perspective))

        doc_edits += (name -> Document.Node.Edits(diff_commands(commands, node2.commands)))

        nodes += (name -> node2)
    }

    (doc_edits.toList, Document.Version.make(syntax, nodes))
  }
}
