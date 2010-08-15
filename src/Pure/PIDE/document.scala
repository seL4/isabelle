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

  object ID {
    def apply(id: ID): String = Markup.Long.apply(id)
    def unapply(s: String): Option[ID] = Markup.Long.unapply(s)
  }

  type Version_ID = ID
  type Command_ID = ID
  type Exec_ID = ID

  val NO_ID: ID = 0



  /** document structure **/

  /* named nodes -- development graph */

  type Node_Text_Edit = (String, List[Text_Edit])  // FIXME None: remove

  type Edit[C] =
   (String,  // node name
    Option[List[(Option[C], Option[C])]])  // None: remove, Some: insert/remove commands

  object Node
  {
    val empty: Node = new Node(Linear_Set())

    // FIXME not scalable
    def command_starts(commands: Iterator[Command], offset: Int = 0): Iterator[(Command, Int)] =
    {
      var i = offset
      for (command <- commands) yield {
        val start = i
        i += command.length
        (command, start)
      }
    }
  }

  class Node(val commands: Linear_Set[Command])
  {
    def command_starts: Iterator[(Command, Int)] =
      Node.command_starts(commands.iterator)

    def command_start(cmd: Command): Option[Int] =
      command_starts.find(_._1 == cmd).map(_._2)

    def command_range(i: Int): Iterator[(Command, Int)] =
      command_starts dropWhile { case (cmd, start) => start + cmd.length <= i }

    def command_range(i: Int, j: Int): Iterator[(Command, Int)] =
      command_range(i) takeWhile { case (_, start) => start < j }

    def command_at(i: Int): Option[(Command, Int)] =
    {
      val range = command_range(i)
      if (range.hasNext) Some(range.next) else None
    }

    def proper_command_at(i: Int): Option[Command] =
      command_at(i) match {
        case Some((command, _)) =>
          commands.reverse_iterator(command).find(cmd => !cmd.is_ignored)
        case None => None
      }
  }



  /** versioning **/

  /* particular document versions */

  object Version
  {
    val init: Version = new Version(NO_ID, Map().withDefaultValue(Node.empty))
  }

  class Version(val id: Version_ID, val nodes: Map[String, Node])


  /* changes of plain text, eventually resulting in document edits */

  object Change
  {
    val init = new Change(Future.value(Version.init), Nil, Future.value(Nil, Version.init))
  }

  class Change(
    val previous: Future[Version],
    val edits: List[Node_Text_Edit],
    val result: Future[(List[Edit[Command]], Version)])
  {
    val current: Future[Version] = result.map(_._2)
    def is_finished: Boolean = previous.is_finished && current.is_finished
  }


  /* history navigation and persistent snapshots */

  abstract class Snapshot
  {
    val version: Version
    val node: Node
    val is_outdated: Boolean
    def convert(offset: Int): Int
    def revert(offset: Int): Int
    def lookup_command(id: Command_ID): Option[Command]
    def state(command: Command): Command.State
  }

  object History
  {
    val init = new History(List(Change.init))
  }

  // FIXME pruning, purging of state
  class History(undo_list: List[Change])
  {
    require(!undo_list.isEmpty)

    def tip: Change = undo_list.head
    def +(ch: Change): History = new History(ch :: undo_list)

    def snapshot(name: String, pending_edits: List[Text_Edit], state_snapshot: State): Snapshot =
    {
      val found_stable = undo_list.find(change =>
        change.is_finished && state_snapshot.is_assigned(change.current.join))
      require(found_stable.isDefined)
      val stable = found_stable.get
      val latest = undo_list.head

      val edits =
        (pending_edits /: undo_list.takeWhile(_ != stable))((edits, change) =>
            (for ((a, eds) <- change.edits if a == name) yield eds).flatten ::: edits)
      lazy val reverse_edits = edits.reverse

      new Snapshot
      {
        val version = stable.current.join
        val node = version.nodes(name)
        val is_outdated = !(pending_edits.isEmpty && latest == stable)
        def convert(offset: Int): Int = (offset /: edits)((i, edit) => edit.convert(i))
        def revert(offset: Int): Int = (offset /: reverse_edits)((i, edit) => edit.revert(i))
        def lookup_command(id: Command_ID): Option[Command] = state_snapshot.lookup_command(id)
        def state(command: Command): Command.State =
          try { state_snapshot.command_state(version, command) }
          catch { case _: State.Fail => command.empty_state }
      }
    }
  }



  /** global state -- document structure and execution process **/

  object State
  {
    class Fail(state: State) extends Exception

    val init = State().define_version(Version.init, Map()).assign(Version.init.id, Nil)

    class Assignment(former_assignment: Map[Command, Exec_ID])
    {
      @volatile private var tmp_assignment = former_assignment
      private val promise = Future.promise[Map[Command, Exec_ID]]
      def is_finished: Boolean = promise.is_finished
      def join: Map[Command, Exec_ID] = promise.join
      def assign(command_execs: List[(Command, Exec_ID)])
      {
        promise.fulfill(tmp_assignment ++ command_execs)
        tmp_assignment = Map()
      }
    }
  }

  case class State(
    val versions: Map[Version_ID, Version] = Map(),
    val commands: Map[Command_ID, Command.State] = Map(),
    val execs: Map[Exec_ID, (Command.State, Set[Version])] = Map(),
    val assignments: Map[Version, State.Assignment] = Map(),
    val disposed: Set[ID] = Set())  // FIXME unused!?
  {
    private def fail[A]: A = throw new State.Fail(this)

    def define_version(version: Version, former_assignment: Map[Command, Exec_ID]): State =
    {
      val id = version.id
      if (versions.isDefinedAt(id) || disposed(id)) fail
      copy(versions = versions + (id -> version),
        assignments = assignments + (version -> new State.Assignment(former_assignment)))
    }

    def define_command(command: Command): State =
    {
      val id = command.id
      if (commands.isDefinedAt(id) || disposed(id)) fail
      copy(commands = commands + (id -> command.empty_state))
    }

    def lookup_command(id: Command_ID): Option[Command] = commands.get(id).map(_.command)

    def the_version(id: Version_ID): Version = versions.getOrElse(id, fail)
    def the_command(id: Command_ID): Command.State = commands.getOrElse(id, fail)
    def the_exec_state(id: Exec_ID): Command.State = execs.getOrElse(id, fail)._1
    def the_assignment(version: Version): State.Assignment = assignments.getOrElse(version, fail)

    def accumulate(id: ID, message: XML.Tree): (Command.State, State) =
      execs.get(id) match {
        case Some((st, occs)) =>
          val new_st = st.accumulate(message)
          (new_st, copy(execs = execs + (id -> (new_st, occs))))
        case None =>
          commands.get(id) match {
            case Some(st) =>
              val new_st = st.accumulate(message)
              (new_st, copy(commands = commands + (id -> new_st)))
            case None => fail
          }
      }

    def assign(id: Version_ID, edits: List[(Command_ID, Exec_ID)]): State =
    {
      val version = the_version(id)
      val occs = Set(version)  // FIXME unused (!?)

      var new_execs = execs
      val assigned_execs =
        for ((cmd_id, exec_id) <- edits) yield {
          val st = the_command(cmd_id)
          if (new_execs.isDefinedAt(exec_id) || disposed(exec_id)) fail
          new_execs += (exec_id -> (st, occs))
          (st.command, exec_id)
        }
      the_assignment(version).assign(assigned_execs)  // FIXME explicit value instead of promise (!?)
      copy(execs = new_execs)
    }

    def is_assigned(version: Version): Boolean =
      assignments.get(version) match {
        case Some(assgn) => assgn.is_finished
        case None => false
      }

    def command_state(version: Version, command: Command): Command.State =
    {
      val assgn = the_assignment(version)
      require(assgn.is_finished)
      the_exec_state(assgn.join.getOrElse(command, fail))
    }
  }
}

