/*  Title:      Pure/PIDE/document.scala
    Author:     Makarius

Document as collection of named nodes, each consisting of an editable
list of commands.
*/

package isabelle


import scala.collection.mutable


object Document
{
  /* formal identifiers */

  type ID = Long
  type Version_ID = ID
  type Command_ID = ID
  type Exec_ID = ID

  val NO_ID: ID = 0

  def parse_id(s: String): ID = java.lang.Long.parseLong(s)
  def print_id(id: ID): String = id.toString



  /** named document nodes **/

  object Node
  {
    val empty: Node = new Node(Linear_Set())

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
    /* command ranges */

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


  /* initial document */

  val init: Document = new Document(NO_ID, Map().withDefaultValue(Node.empty))



  /** changes of plain text, eventually resulting in document edits **/

  type Node_Text_Edit = (String, List[Text_Edit])  // FIXME None: remove

  type Edit[C] =
   (String,  // node name
    Option[List[(Option[C], Option[C])]])  // None: remove, Some: insert/remove commands

  abstract class Snapshot
  {
    val document: Document
    val node: Document.Node
    val is_outdated: Boolean
    def convert(offset: Int): Int
    def revert(offset: Int): Int
    def lookup_command(id: Command_ID): Option[Command]
    def state(command: Command): Command.State
  }

  object Change
  {
    val init = new Change(Future.value(Document.init), Nil, Future.value(Nil, Document.init))
  }

  class Change(
    val prev: Future[Document],
    val edits: List[Node_Text_Edit],
    val result: Future[(List[Edit[Command]], Document)])
  {
    val document: Future[Document] = result.map(_._2)
    def is_finished: Boolean = prev.is_finished && document.is_finished
  }



  /** global state -- accumulated prover results **/

  object State
  {
    class Fail(state: State) extends Exception

    val init = State().define_document(Document.init, Map()).assign(Document.init.id, Nil)

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
    val documents: Map[Version_ID, Document] = Map(),
    val commands: Map[Command_ID, Command.State] = Map(),
    val execs: Map[Exec_ID, (Command.State, Set[Document])] = Map(),
    val assignments: Map[Document, State.Assignment] = Map(),
    val disposed: Set[ID] = Set())  // FIXME unused!?
  {
    private def fail[A]: A = throw new State.Fail(this)

    def define_document(document: Document, former_assignment: Map[Command, Exec_ID]): State =
    {
      val id = document.id
      if (documents.isDefinedAt(id) || disposed(id)) fail
      copy(documents = documents + (id -> document),
        assignments = assignments + (document -> new State.Assignment(former_assignment)))
    }

    def define_command(command: Command): State =
    {
      val id = command.id
      if (commands.isDefinedAt(id) || disposed(id)) fail
      copy(commands = commands + (id -> command.empty_state))
    }

    def lookup_command(id: Command_ID): Option[Command] = commands.get(id).map(_.command)

    def the_document(id: Version_ID): Document = documents.getOrElse(id, fail)
    def the_command(id: Command_ID): Command.State = commands.getOrElse(id, fail)
    def the_exec_state(id: Exec_ID): Command.State = execs.getOrElse(id, fail)._1
    def the_assignment(document: Document): State.Assignment = assignments.getOrElse(document, fail)

    def accumulate(id: ID, message: XML.Tree): (Command.State, State) =
      execs.get(id) match {
        case Some((st, docs)) =>
          val new_st = st.accumulate(message)
          (new_st, copy(execs = execs + (id -> (new_st, docs))))
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
      val doc = the_document(id)
      val docs = Set(doc)  // FIXME unused (!?)

      var new_execs = execs
      val assigned_execs =
        for ((cmd_id, exec_id) <- edits) yield {
          val st = the_command(cmd_id)
          if (new_execs.isDefinedAt(exec_id) || disposed(exec_id)) fail
          new_execs += (exec_id -> (st, docs))
          (st.command, exec_id)
        }
      the_assignment(doc).assign(assigned_execs)  // FIXME explicit value instead of promise (!?)
      copy(execs = new_execs)
    }

    def is_assigned(document: Document): Boolean =
      assignments.get(document) match {
        case Some(assgn) => assgn.is_finished
        case None => false
      }

    def command_state(document: Document, command: Command): Command.State =
    {
      val assgn = the_assignment(document)
      require(assgn.is_finished)
      the_exec_state(assgn.join.getOrElse(command, fail))
    }
  }
}


class Document(
    val id: Document.Version_ID,
    val nodes: Map[String, Document.Node])

