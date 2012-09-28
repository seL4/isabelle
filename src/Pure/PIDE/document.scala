/*  Title:      Pure/PIDE/document.scala
    Author:     Makarius

Document as collection of named nodes, each consisting of an editable
list of commands, associated with asynchronous execution process.
*/

package isabelle


import scala.collection.mutable


object Document
{
  /* formal identifiers */

  type ID = Long
  val ID = Properties.Value.Long

  type Version_ID = ID
  type Command_ID = ID
  type Exec_ID = ID

  val no_id: ID = 0
  val new_id = Counter()



  /** document structure **/

  /* individual nodes */

  type Edit[A, B] = (Node.Name, Node.Edit[A, B])
  type Edit_Text = Edit[Text.Edit, Text.Perspective]
  type Edit_Command = Edit[(Option[Command], Option[Command]), Command.Perspective]

  object Node
  {
    sealed case class Header(
      imports: List[Name],
      keywords: Thy_Header.Keywords,
      uses: List[(String, Boolean)],
      errors: List[String] = Nil)
    {
      def error(msg: String): Header = copy(errors = errors ::: List(msg))
    }

    def bad_header(msg: String): Header = Header(Nil, Nil, Nil, List(msg))

    object Name
    {
      val empty = Name("", "", "")
      def apply(raw_path: Path): Name =
      {
        val path = raw_path.expand
        val node = path.implode
        val dir = path.dir.implode
        val theory = Thy_Header.thy_name(node) getOrElse error("Bad theory file name: " + path)
        Name(node, dir, theory)
      }

      object Ordering extends scala.math.Ordering[Name]
      {
        def compare(name1: Name, name2: Name): Int = name1.node compare name2.node
      }
    }
    sealed case class Name(node: String, dir: String, theory: String)
    {
      override def hashCode: Int = node.hashCode
      override def equals(that: Any): Boolean =
        that match {
          case other: Name => node == other.node
          case _ => false
        }
      override def toString: String = theory
    }

    sealed abstract class Edit[A, B]
    {
      def foreach(f: A => Unit)
      {
        this match {
          case Edits(es) => es.foreach(f)
          case _ =>
        }
      }
    }
    case class Clear[A, B]() extends Edit[A, B]
    case class Edits[A, B](edits: List[A]) extends Edit[A, B]
    case class Deps[A, B](header: Header) extends Edit[A, B]
    case class Perspective[A, B](perspective: B) extends Edit[A, B]

    def command_starts(commands: Iterator[Command], offset: Text.Offset = 0)
      : Iterator[(Command, Text.Offset)] =
    {
      var i = offset
      for (command <- commands) yield {
        val start = i
        i += command.length
        (command, start)
      }
    }

    private val block_size = 1024

    val empty: Node = new Node()
  }

  final class Node private(
    val header: Node.Header = Node.bad_header("Bad theory header"),
    val perspective: Command.Perspective = Command.Perspective.empty,
    val blobs: Map[String, Blob] = Map.empty,
    val commands: Linear_Set[Command] = Linear_Set.empty)
  {
    def clear: Node = new Node(header = header)

    def update_header(new_header: Node.Header): Node =
      new Node(new_header, perspective, blobs, commands)

    def update_perspective(new_perspective: Command.Perspective): Node =
      new Node(header, new_perspective, blobs, commands)

    def update_blobs(new_blobs: Map[String, Blob]): Node =
      new Node(header, perspective, new_blobs, commands)

    def update_commands(new_commands: Linear_Set[Command]): Node =
      new Node(header, perspective, blobs, new_commands)


    /* commands */

    private lazy val full_index: (Array[(Command, Text.Offset)], Text.Range) =
    {
      val blocks = new mutable.ListBuffer[(Command, Text.Offset)]
      var next_block = 0
      var last_stop = 0
      for ((command, start) <- Node.command_starts(commands.iterator)) {
        last_stop = start + command.length
        while (last_stop + 1 > next_block) {
          blocks += (command -> start)
          next_block += Node.block_size
        }
      }
      (blocks.toArray, Text.Range(0, last_stop))
    }

    def full_range: Text.Range = full_index._2

    def command_range(i: Text.Offset = 0): Iterator[(Command, Text.Offset)] =
    {
      if (!commands.isEmpty && full_range.contains(i)) {
        val (cmd0, start0) = full_index._1(i / Node.block_size)
        Node.command_starts(commands.iterator(cmd0), start0) dropWhile {
          case (cmd, start) => start + cmd.length <= i }
      }
      else Iterator.empty
    }

    def command_range(range: Text.Range): Iterator[(Command, Text.Offset)] =
      command_range(range.start) takeWhile { case (_, start) => start < range.stop }

    def command_at(i: Text.Offset): Option[(Command, Text.Offset)] =
    {
      val range = command_range(i)
      if (range.hasNext) Some(range.next) else None
    }

    def command_start(cmd: Command): Option[Text.Offset] =
      Node.command_starts(commands.iterator).find(_._1 == cmd).map(_._2)
  }


  /* development graph */

  object Nodes
  {
    val empty: Nodes = new Nodes(Graph.empty(Node.Name.Ordering))
  }

  final class Nodes private(graph: Graph[Node.Name, Node])
  {
    def get_name(s: String): Option[Node.Name] =
      graph.keys.find(name => name.node == s)

    def apply(name: Node.Name): Node =
      graph.default_node(name, Node.empty).get_node(name)

    def + (entry: (Node.Name, Node)): Nodes =
    {
      val (name, node) = entry
      val imports = node.header.imports
      val graph1 =
        (graph.default_node(name, Node.empty) /: imports)((g, p) => g.default_node(p, Node.empty))
      val graph2 = (graph1 /: graph1.imm_preds(name))((g, dep) => g.del_edge(dep, name))
      val graph3 = (graph2 /: imports)((g, dep) => g.add_edge(dep, name))
      new Nodes(graph3.map_node(name, _ => node))
    }

    def entries: Iterator[(Node.Name, Node)] =
      graph.entries.map({ case (name, (node, _)) => (name, node) })

    def descendants(names: List[Node.Name]): List[Node.Name] = graph.all_succs(names)
    def topological_order: List[Node.Name] = graph.topological_order
  }



  /** versioning **/

  /* particular document versions */

  object Version
  {
    val init: Version = new Version()

    def make(syntax: Outer_Syntax, nodes: Nodes): Version =
      new Version(new_id(), syntax, nodes)
  }

  final class Version private(
    val id: Version_ID = no_id,
    val syntax: Outer_Syntax = Outer_Syntax.empty,
    val nodes: Nodes = Nodes.empty)
  {
    def is_init: Boolean = id == no_id
  }


  /* changes of plain text, eventually resulting in document edits */

  object Change
  {
    val init: Change = new Change()

    def make(previous: Future[Version], edits: List[Edit_Text], version: Future[Version]): Change =
      new Change(Some(previous), edits, version)
  }

  final class Change private(
    val previous: Option[Future[Version]] = Some(Future.value(Version.init)),
    val edits: List[Edit_Text] = Nil,
    val version: Future[Version] = Future.value(Version.init))
  {
    def is_finished: Boolean =
      (previous match { case None => true case Some(future) => future.is_finished }) &&
      version.is_finished

    def truncate: Change = new Change(None, Nil, version)
  }


  /* history navigation */

  object History
  {
    val init: History = new History()
  }

  final class History private(
    val undo_list: List[Change] = List(Change.init))  // non-empty list
  {
    def tip: Change = undo_list.head
    def + (change: Change): History = new History(change :: undo_list)

    def prune(check: Change => Boolean, retain: Int): Option[(List[Change], History)] =
    {
      val n = undo_list.iterator.zipWithIndex.find(p => check(p._1)).get._2 + 1
      val (retained, dropped) = undo_list.splitAt(n max retain)

      retained.splitAt(retained.length - 1) match {
        case (prefix, List(last)) => Some(dropped, new History(prefix ::: List(last.truncate)))
        case _ => None
      }
    }
  }



  /** global state -- document structure, execution process, editing history **/

  abstract class Snapshot
  {
    val state: State
    val version: Version
    val node_name: Node.Name
    val node: Node
    val is_outdated: Boolean
    def convert(i: Text.Offset): Text.Offset
    def convert(range: Text.Range): Text.Range
    def revert(i: Text.Offset): Text.Offset
    def revert(range: Text.Range): Text.Range
    def eq_markup(other: Snapshot): Boolean
    def cumulate_markup[A](range: Text.Range, info: A, elements: Option[Set[String]],
      result: PartialFunction[(A, Text.Markup), A]): Stream[Text.Info[A]]
    def select_markup[A](range: Text.Range, elements: Option[Set[String]],
      result: PartialFunction[Text.Markup, A]): Stream[Text.Info[A]]
  }

  type Assign = List[(Document.Command_ID, Option[Document.Exec_ID])]  // exec state assignment

  object State
  {
    class Fail(state: State) extends Exception

    object Assignment
    {
      val init: Assignment = new Assignment()
    }

    final class Assignment private(
      val command_execs: Map[Command_ID, Exec_ID] = Map.empty,
      val is_finished: Boolean = false)
    {
      def check_finished: Assignment = { require(is_finished); this }
      def unfinished: Assignment = new Assignment(command_execs, false)

      def assign(add_command_execs: List[(Command_ID, Option[Exec_ID])]): Assignment =
      {
        require(!is_finished)
        val command_execs1 =
          (command_execs /: add_command_execs) {
            case (res, (command_id, None)) => res - command_id
            case (res, (command_id, Some(exec_id))) => res + (command_id -> exec_id)
          }
        new Assignment(command_execs1, true)
      }
    }

    val init: State =
      State().define_version(Version.init, Assignment.init).assign(Version.init.id)._2
  }

  final case class State private(
    val versions: Map[Version_ID, Version] = Map.empty,
    val commands: Map[Command_ID, Command.State] = Map.empty,  // static markup from define_command
    val execs: Map[Exec_ID, Command.State] = Map.empty,  // dynamic markup from execution
    val assignments: Map[Version_ID, State.Assignment] = Map.empty,
    val history: History = History.init)
  {
    private def fail[A]: A = throw new State.Fail(this)

    def define_version(version: Version, assignment: State.Assignment): State =
    {
      val id = version.id
      copy(versions = versions + (id -> version),
        assignments = assignments + (id -> assignment.unfinished))
    }

    def define_command(command: Command): State =
    {
      val id = command.id
      copy(commands = commands + (id -> command.init_state))
    }

    def defined_command(id: Command_ID): Boolean = commands.isDefinedAt(id)

    def find_command(version: Version, id: ID): Option[(Node, Command)] =
      commands.get(id) orElse execs.get(id) match {
        case None => None
        case Some(st) =>
          val command = st.command
          val node = version.nodes(command.node_name)
          Some((node, command))
      }

    def the_version(id: Version_ID): Version = versions.getOrElse(id, fail)
    def the_command_state(id: Command_ID): Command.State = commands.getOrElse(id, fail)
    def the_exec(id: Exec_ID): Command.State = execs.getOrElse(id, fail)
    def the_assignment(version: Version): State.Assignment =
      assignments.getOrElse(version.id, fail)

    def accumulate(id: ID, message: XML.Elem): (Command.State, State) =
      execs.get(id) match {
        case Some(st) =>
          val new_st = st + (id, message)
          (new_st, copy(execs = execs + (id -> new_st)))
        case None =>
          commands.get(id) match {
            case Some(st) =>
              val new_st = st + (id, message)
              (new_st, copy(commands = commands + (id -> new_st)))
            case None => fail
          }
      }

    def assign(id: Version_ID, command_execs: Assign = Nil): (List[Command], State) =
    {
      val version = the_version(id)

      val (changed_commands, new_execs) =
        ((Nil: List[Command], execs) /: command_execs) {
          case ((commands1, execs1), (cmd_id, exec)) =>
            val st = the_command_state(cmd_id)
            val commands2 = st.command :: commands1
            val execs2 =
              exec match {
                case None => execs1
                case Some(exec_id) => execs1 + (exec_id -> st)
              }
            (commands2, execs2)
        }
      val new_assignment = the_assignment(version).assign(command_execs)
      val new_state = copy(assignments = assignments + (id -> new_assignment), execs = new_execs)

      (changed_commands, new_state)
    }

    def is_assigned(version: Version): Boolean =
      assignments.get(version.id) match {
        case Some(assgn) => assgn.is_finished
        case None => false
      }

    def is_stable(change: Change): Boolean =
      change.is_finished && is_assigned(change.version.get_finished)

    def recent_finished: Change = history.undo_list.find(_.is_finished) getOrElse fail
    def recent_stable: Change = history.undo_list.find(is_stable) getOrElse fail
    def tip_stable: Boolean = is_stable(history.tip)
    def tip_version: Version = history.tip.version.get_finished

    def continue_history(
        previous: Future[Version],
        edits: List[Edit_Text],
        version: Future[Version]): (Change, State) =
    {
      val change = Change.make(previous, edits, version)
      (change, copy(history = history + change))
    }

    def prune_history(retain: Int = 0): (List[Version], State) =
    {
      history.prune(is_stable, retain) match {
        case Some((dropped, history1)) =>
          val dropped_versions = dropped.map(change => change.version.get_finished)
          val state1 = copy(history = history1)
          (dropped_versions, state1)
        case None => fail
      }
    }

    def removed_versions(removed: List[Version_ID]): State =
    {
      val versions1 = versions -- removed
      val assignments1 = assignments -- removed
      var commands1 = Map.empty[Command_ID, Command.State]
      var execs1 = Map.empty[Exec_ID, Command.State]
      for {
        (version_id, version) <- versions1.iterator
        command_execs = assignments1(version_id).command_execs
        (_, node) <- version.nodes.entries
        command <- node.commands.iterator
      } {
        val id = command.id
        if (!commands1.isDefinedAt(id) && commands.isDefinedAt(id))
          commands1 += (id -> commands(id))
        if (command_execs.isDefinedAt(id)) {
          val exec_id = command_execs(id)
          if (!execs1.isDefinedAt(exec_id) && execs.isDefinedAt(exec_id))
            execs1 += (exec_id -> execs(exec_id))
        }
      }
      copy(versions = versions1, commands = commands1, execs = execs1, assignments = assignments1)
    }

    def command_state(version: Version, command: Command): Command.State =
    {
      require(is_assigned(version))
      try {
        the_exec(the_assignment(version).check_finished.command_execs
          .getOrElse(command.id, fail))
      }
      catch {
        case _: State.Fail =>
          try { the_command_state(command.id) }
          catch { case _: State.Fail => command.init_state }
      }
    }

    def markup_to_XML(version: Version, node: Node, filter: XML.Elem => Boolean): XML.Body =
      node.commands.toList.map(cmd => command_state(version, cmd).markup_to_XML(filter)).flatten

    // persistent user-view
    def snapshot(name: Node.Name = Node.Name.empty, pending_edits: List[Text.Edit] = Nil)
      : Snapshot =
    {
      val stable = recent_stable
      val latest = history.tip

      // FIXME proper treatment of removed nodes
      val edits =
        (pending_edits /: history.undo_list.takeWhile(_ != stable))((edits, change) =>
            (for ((a, Node.Edits(es)) <- change.edits if a == name) yield es).flatten ::: edits)
      lazy val reverse_edits = edits.reverse

      new Snapshot
      {
        val state = State.this
        val version = stable.version.get_finished
        val node_name = name
        val node = version.nodes(name)
        val is_outdated = !(pending_edits.isEmpty && latest == stable)

        def convert(offset: Text.Offset) = (offset /: edits)((i, edit) => edit.convert(i))
        def revert(offset: Text.Offset) = (offset /: reverse_edits)((i, edit) => edit.revert(i))
        def convert(range: Text.Range) = (range /: edits)((r, edit) => edit.convert(r))
        def revert(range: Text.Range) = (range /: reverse_edits)((r, edit) => edit.revert(r))

        def eq_markup(other: Snapshot): Boolean =
          !is_outdated && !other.is_outdated &&
            node.commands.size == other.node.commands.size &&
            ((node.commands.iterator zip other.node.commands.iterator) forall {
              case (cmd1, cmd2) =>
                cmd1.source == cmd2.source &&
                (state.command_state(version, cmd1).markup eq
                 other.state.command_state(other.version, cmd2).markup)
            })

        def cumulate_markup[A](range: Text.Range, info: A, elements: Option[Set[String]],
          result: PartialFunction[(A, Text.Markup), A]): Stream[Text.Info[A]] =
        {
          val former_range = revert(range)
          for {
            (command, command_start) <- node.command_range(former_range).toStream
            Text.Info(r0, a) <- state.command_state(version, command).markup.
              cumulate[A]((former_range - command_start).restrict(command.range), info, elements,
                {
                  case (a, Text.Info(r0, b))
                  if result.isDefinedAt((a, Text.Info(convert(r0 + command_start), b))) =>
                    result((a, Text.Info(convert(r0 + command_start), b)))
                })
          } yield Text.Info(convert(r0 + command_start), a)
        }

        def select_markup[A](range: Text.Range, elements: Option[Set[String]],
          result: PartialFunction[Text.Markup, A]): Stream[Text.Info[A]] =
        {
          val result1 =
            new PartialFunction[(Option[A], Text.Markup), Option[A]] {
              def isDefinedAt(arg: (Option[A], Text.Markup)): Boolean = result.isDefinedAt(arg._2)
              def apply(arg: (Option[A], Text.Markup)): Option[A] = Some(result(arg._2))
            }
          for (Text.Info(r, Some(x)) <- cumulate_markup(range, None, elements, result1))
            yield Text.Info(r, x)
        }
      }
    }
  }
}

