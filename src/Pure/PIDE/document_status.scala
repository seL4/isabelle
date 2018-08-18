/*  Title:      Pure/PIDE/document_status.scala
    Author:     Makarius

Document status based on markup information.
*/

package isabelle


object Document_Status
{
  /* command status */

  object Command_Status
  {
    val proper_elements: Markup.Elements =
      Markup.Elements(Markup.ACCEPTED, Markup.FORKED, Markup.JOINED, Markup.RUNNING,
        Markup.FINISHED, Markup.FAILED)

    val liberal_elements: Markup.Elements =
      proper_elements + Markup.WARNING + Markup.LEGACY + Markup.ERROR

    def make(markup_iterator: Iterator[Markup]): Command_Status =
    {
      var touched = false
      var accepted = false
      var warned = false
      var failed = false
      var forks = 0
      var runs = 0
      for (markup <- markup_iterator) {
        markup.name match {
          case Markup.ACCEPTED => accepted = true
          case Markup.FORKED => touched = true; forks += 1
          case Markup.JOINED => forks -= 1
          case Markup.RUNNING => touched = true; runs += 1
          case Markup.FINISHED => runs -= 1
          case Markup.WARNING | Markup.LEGACY => warned = true
          case Markup.FAILED | Markup.ERROR => failed = true
          case _ =>
        }
      }
      Command_Status(touched, accepted, warned, failed, forks, runs)
    }

    val empty = make(Iterator.empty)

    def merge(status_iterator: Iterator[Command_Status]): Command_Status =
      if (status_iterator.hasNext) {
        val status0 = status_iterator.next
        (status0 /: status_iterator)(_ + _)
      }
      else empty
  }

  sealed case class Command_Status(
    private val touched: Boolean,
    private val accepted: Boolean,
    private val warned: Boolean,
    private val failed: Boolean,
    forks: Int,
    runs: Int)
  {
    def + (that: Command_Status): Command_Status =
      Command_Status(
        touched || that.touched,
        accepted || that.accepted,
        warned || that.warned,
        failed || that.failed,
        forks + that.forks,
        runs + that.runs)

    def is_unprocessed: Boolean = accepted && !failed && (!touched || (forks != 0 && runs == 0))
    def is_running: Boolean = runs != 0
    def is_warned: Boolean = warned
    def is_failed: Boolean = failed
    def is_finished: Boolean = !failed && touched && forks == 0 && runs == 0
  }


  /* node status */

  object Node_Status
  {
    def make(
      state: Document.State,
      version: Document.Version,
      name: Document.Node.Name): Node_Status =
    {
      val node = version.nodes(name)

      var unprocessed = 0
      var running = 0
      var warned = 0
      var failed = 0
      var finished = 0
      for (command <- node.commands.iterator) {
        val states = state.command_states(version, command)
        val status = Command_Status.merge(states.iterator.map(_.document_status))

        if (status.is_running) running += 1
        else if (status.is_failed) failed += 1
        else if (status.is_warned) warned += 1
        else if (status.is_finished) finished += 1
        else unprocessed += 1
      }
      val initialized = state.node_initialized(version, name)
      val consolidated = state.node_consolidated(version, name)

      Node_Status(unprocessed, running, warned, failed, finished, initialized, consolidated)
    }
  }

  sealed case class Node_Status(
    unprocessed: Int, running: Int, warned: Int, failed: Int, finished: Int,
    initialized: Boolean, consolidated: Boolean)
  {
    def ok: Boolean = failed == 0
    def total: Int = unprocessed + running + warned + failed + finished

    def json: JSON.Object.T =
      JSON.Object("ok" -> ok, "total" -> total, "unprocessed" -> unprocessed,
        "running" -> running, "warned" -> warned, "failed" -> failed, "finished" -> finished,
        "initialized" -> initialized, "consolidated" -> consolidated)
  }


  /* node timing */

  object Node_Timing
  {
    val empty: Node_Timing = Node_Timing(0.0, Map.empty)

    def make(
      state: Document.State,
      version: Document.Version,
      node: Document.Node,
      threshold: Double): Node_Timing =
    {
      var total = 0.0
      var commands = Map.empty[Command, Double]
      for {
        command <- node.commands.iterator
        st <- state.command_states(version, command)
      } {
        val command_timing =
          (0.0 /: st.status)({
            case (timing, Markup.Timing(t)) => timing + t.elapsed.seconds
            case (timing, _) => timing
          })
        total += command_timing
        if (command_timing >= threshold) commands += (command -> command_timing)
      }
      Node_Timing(total, commands)
    }
  }

  sealed case class Node_Timing(total: Double, commands: Map[Command, Double])


  /* nodes status */

  object Overall_Node_Status extends Enumeration
  {
    val ok, failed, pending = Value
  }

  object Nodes_Status
  {
    val empty: Nodes_Status = new Nodes_Status(Map.empty)
  }

  final class Nodes_Status private(private val rep: Map[Document.Node.Name, Node_Status])
  {
    def get(name: Document.Node.Name): Option[Node_Status] = rep.get(name)

    def overall_node_status(name: Document.Node.Name): Overall_Node_Status.Value =
      rep.get(name) match {
        case Some(st) if st.consolidated =>
          if (st.ok) Overall_Node_Status.ok else Overall_Node_Status.failed
        case _ => Overall_Node_Status.pending
      }

    def update(
      session_base: Sessions.Base,
      state: Document.State,
      version: Document.Version,
      domain: Option[Set[Document.Node.Name]],
      trim: Boolean): Option[(Nodes_Status, List[Document.Node.Name])] =
    {
      val nodes = version.nodes
      val update_iterator =
        for {
          name <- domain.getOrElse(nodes.domain).iterator
          if !Sessions.is_hidden(name) &&
              !session_base.loaded_theory(name) &&
              !nodes.is_suppressed(name) &&
              !nodes(name).is_empty
          st = Document_Status.Node_Status.make(state, version, name)
          if !rep.isDefinedAt(name) || rep(name) != st
        } yield (name -> st)
      val rep1 = rep ++ update_iterator
      val rep2 = if (trim) rep1 -- rep1.keysIterator.filterNot(nodes.domain) else rep1

      if (rep == rep2) None
      else Some(new Nodes_Status(rep2), version.nodes.topological_order.filter(rep2.keySet))
    }

    override def hashCode: Int = rep.hashCode
    override def equals(that: Any): Boolean =
      that match {
        case other: Nodes_Status => rep == other.rep
        case _ => false
      }

    override def toString: String =
    {
      var ok = 0
      var failed = 0
      var pending = 0
      for (name <- rep.keysIterator) {
        overall_node_status(name) match {
          case Overall_Node_Status.ok => ok += 1
          case Overall_Node_Status.failed => failed += 1
          case Overall_Node_Status.pending => pending += 1
        }
      }
      "Nodes_Status(ok = " + ok + ", failed = " + failed + ", pending = " + pending + ")"
    }
  }
}
