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
        Markup.FINISHED, Markup.FAILED, Markup.CANCELED)

    val liberal_elements: Markup.Elements =
      proper_elements + Markup.WARNING + Markup.LEGACY + Markup.ERROR

    def make(markup_iterator: Iterator[Markup]): Command_Status =
    {
      var touched = false
      var accepted = false
      var warned = false
      var failed = false
      var canceled = false
      var finalized = false
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
          case Markup.CANCELED => canceled = true
          case Markup.FINALIZED => finalized = true
          case _ =>
        }
      }
      Command_Status(
        touched = touched,
        accepted = accepted,
        warned = warned,
        failed = failed,
        canceled = canceled,
        finalized = finalized,
        forks = forks,
        runs = runs)
    }

    val empty: Command_Status = make(Iterator.empty)

    def merge(status_iterator: Iterator[Command_Status]): Command_Status =
      if (status_iterator.hasNext) {
        val status0 = status_iterator.next()
        (status0 /: status_iterator)(_ + _)
      }
      else empty
  }

  sealed case class Command_Status(
    private val touched: Boolean,
    private val accepted: Boolean,
    private val warned: Boolean,
    private val failed: Boolean,
    private val canceled: Boolean,
    private val finalized: Boolean,
    forks: Int,
    runs: Int)
  {
    def + (that: Command_Status): Command_Status =
      Command_Status(
        touched = touched || that.touched,
        accepted = accepted || that.accepted,
        warned = warned || that.warned,
        failed = failed || that.failed,
        canceled = canceled || that.canceled,
        finalized = finalized || that.finalized,
        forks = forks + that.forks,
        runs = runs + that.runs)

    def is_unprocessed: Boolean = accepted && !failed && (!touched || (forks != 0 && runs == 0))
    def is_running: Boolean = runs != 0
    def is_warned: Boolean = warned
    def is_failed: Boolean = failed
    def is_finished: Boolean = !failed && touched && forks == 0 && runs == 0
    def is_canceled: Boolean = canceled
    def is_finalized: Boolean = finalized
    def is_terminated: Boolean = canceled || touched && forks == 0 && runs == 0
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
      var canceled = false
      var terminated = true
      var finalized = false
      for (command <- node.commands.iterator) {
        val states = state.command_states(version, command)
        val status = Command_Status.merge(states.iterator.map(_.document_status))

        if (status.is_running) running += 1
        else if (status.is_failed) failed += 1
        else if (status.is_warned) warned += 1
        else if (status.is_finished) finished += 1
        else unprocessed += 1

        if (status.is_canceled) canceled = true
        if (!status.is_terminated) terminated = false
        if (status.is_finalized) finalized = true
      }
      val initialized = state.node_initialized(version, name)
      val consolidated = state.node_consolidated(version, name)

      Node_Status(
        is_suppressed = version.nodes.is_suppressed(name),
        unprocessed = unprocessed,
        running = running,
        warned = warned,
        failed = failed,
        finished = finished,
        canceled = canceled,
        terminated = terminated,
        initialized = initialized,
        finalized = finalized,
        consolidated = consolidated)
    }
  }

  sealed case class Node_Status(
    is_suppressed: Boolean,
    unprocessed: Int,
    running: Int,
    warned: Int,
    failed: Int,
    finished: Int,
    canceled: Boolean,
    terminated: Boolean,
    initialized: Boolean,
    finalized: Boolean,
    consolidated: Boolean)
  {
    def ok: Boolean = failed == 0
    def total: Int = unprocessed + running + warned + failed + finished

    def quasi_consolidated: Boolean = !is_suppressed && !finalized && terminated

    def percentage: Int =
      if (consolidated) 100
      else if (total == 0) 0
      else (((total - unprocessed).toDouble / total) * 100).toInt min 99

    def json: JSON.Object.T =
      JSON.Object("ok" -> ok, "total" -> total, "unprocessed" -> unprocessed,
        "running" -> running, "warned" -> warned, "failed" -> failed, "finished" -> finished,
        "canceled" -> canceled, "consolidated" -> consolidated,
        "percentage" -> percentage)
  }


  /* overall timing */

  object Overall_Timing
  {
    val empty: Overall_Timing = Overall_Timing(0.0, Map.empty)

    def make(
      state: Document.State,
      version: Document.Version,
      commands: Iterable[Command],
      threshold: Double = 0.0): Overall_Timing =
    {
      var total = 0.0
      var command_timings = Map.empty[Command, Double]
      for {
        command <- commands.iterator
        st <- state.command_states(version, command)
      } {
        val command_timing =
          (0.0 /: st.status)({
            case (timing, Markup.Timing(t)) => timing + t.elapsed.seconds
            case (timing, _) => timing
          })
        total += command_timing
        if (command_timing > 0.0 && command_timing >= threshold) {
          command_timings += (command -> command_timing)
        }
      }
      Overall_Timing(total, command_timings)
    }
  }

  sealed case class Overall_Timing(total: Double, command_timings: Map[Command, Double])
  {
    def command_timing(command: Command): Double =
      command_timings.getOrElse(command, 0.0)
  }


  /* nodes status */

  object Overall_Node_Status extends Enumeration
  {
    val ok, failed, pending = Value
  }

  object Nodes_Status
  {
    val empty: Nodes_Status = new Nodes_Status(Map.empty, Document.Nodes.empty)
  }

  final class Nodes_Status private(
    private val rep: Map[Document.Node.Name, Node_Status],
    nodes: Document.Nodes)
  {
    def is_empty: Boolean = rep.isEmpty
    def apply(name: Document.Node.Name): Node_Status = rep(name)
    def get(name: Document.Node.Name): Option[Node_Status] = rep.get(name)

    def present: List[(Document.Node.Name, Node_Status)] =
      (for {
        name <- nodes.topological_order.iterator
        node_status <- get(name)
      } yield (name, node_status)).toList

    def quasi_consolidated(name: Document.Node.Name): Boolean =
      rep.get(name) match {
        case Some(st) => st.quasi_consolidated
        case None => false
      }

    def overall_node_status(name: Document.Node.Name): Overall_Node_Status.Value =
      rep.get(name) match {
        case Some(st) if st.consolidated =>
          if (st.ok) Overall_Node_Status.ok else Overall_Node_Status.failed
        case _ => Overall_Node_Status.pending
      }

    def update(
      resources: Resources,
      state: Document.State,
      version: Document.Version,
      domain: Option[Set[Document.Node.Name]] = None,
      trim: Boolean = false): (Boolean, Nodes_Status) =
    {
      val nodes1 = version.nodes
      val update_iterator =
        for {
          name <- domain.getOrElse(nodes1.domain).iterator
          if !resources.is_hidden(name) && !resources.session_base.loaded_theory(name)
          st = Document_Status.Node_Status.make(state, version, name)
          if !rep.isDefinedAt(name) || rep(name) != st
        } yield (name -> st)
      val rep1 = rep ++ update_iterator
      val rep2 = if (trim) rep1 -- rep1.keysIterator.filterNot(nodes1.domain) else rep1

      (rep != rep2, new Nodes_Status(rep2, nodes1))
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
      var canceled = 0
      for (name <- rep.keysIterator) {
        overall_node_status(name) match {
          case Overall_Node_Status.ok => ok += 1
          case Overall_Node_Status.failed => failed += 1
          case Overall_Node_Status.pending => pending += 1
        }
        if (apply(name).canceled) canceled += 1
      }
      "Nodes_Status(ok = " + ok + ", failed = " + failed + ", pending = " + pending +
        ", canceled = " + canceled + ")"
    }
  }
}
