/*  Title:      Pure/PIDE/document_status.scala
    Author:     Makarius

Document status based on markup information.
*/

package isabelle


object Document_Status {
  /* theory status: via 'theory' or 'end' commands */

  object Theory_Status extends Enumeration {
    val NONE, INITIALIZED, FINALIZED, CONSOLIDATING, CONSOLIDATED = Value

    def initialized(t: Value): Boolean = t >= INITIALIZED
    def finalized(t: Value): Boolean = t >= FINALIZED
    def consolidating(t: Value): Boolean = t >= CONSOLIDATING
    def consolidated(t: Value): Boolean = t >= CONSOLIDATED

    def merge(t1: Value, t2: Value): Value = if (t1 >= t2) t1 else t2
  }

  trait Theory_Status {
    def theory_status: Theory_Status.Value
    def initialized: Boolean = Theory_Status.initialized(theory_status)
    def finalized: Boolean = Theory_Status.finalized(theory_status)
    def consolidating: Boolean = Theory_Status.consolidating(theory_status)
    def consolidated: Boolean = Theory_Status.consolidated(theory_status)
  }


  /* command status */

  object Command_Status {
    val proper_elements: Markup.Elements =
      Markup.Elements(Markup.ACCEPTED, Markup.FORKED, Markup.JOINED, Markup.RUNNING,
        Markup.FINISHED, Markup.FAILED, Markup.CANCELED)

    val liberal_elements: Markup.Elements =
      proper_elements + Markup.WARNING + Markup.LEGACY + Markup.ERROR

    def make(
      markups: Iterable[Markup],
      warned: Boolean = false,
      failed: Boolean = false
    ): Command_Status = {
      var theory_status = Theory_Status.NONE
      var touched = false
      var accepted = false
      var warned1 = warned
      var failed1 = failed
      var canceled = false
      var forks = 0
      var runs = 0
      for (markup <- markups) {
        markup.name match {
          case Markup.INITIALIZED =>
            theory_status = Theory_Status.merge(theory_status, Theory_Status.INITIALIZED)
          case Markup.FINALIZED =>
            theory_status = Theory_Status.merge(theory_status, Theory_Status.FINALIZED)
          case Markup.CONSOLIDATING =>
            theory_status = Theory_Status.merge(theory_status, Theory_Status.CONSOLIDATING)
          case Markup.CONSOLIDATED =>
            theory_status = Theory_Status.merge(theory_status, Theory_Status.CONSOLIDATED)
          case Markup.ACCEPTED => accepted = true
          case Markup.FORKED => touched = true; forks += 1
          case Markup.JOINED => forks -= 1
          case Markup.RUNNING => touched = true; runs += 1
          case Markup.FINISHED => runs -= 1
          case Markup.WARNING | Markup.LEGACY => warned1 = true
          case Markup.FAILED | Markup.ERROR => failed1 = true
          case Markup.CANCELED => canceled = true
          case _ =>
        }
      }
      new Command_Status(
        theory_status = theory_status,
        touched = touched,
        accepted = accepted,
        warned = warned1,
        failed = failed1,
        canceled = canceled,
        forks = forks,
        runs = runs)
    }

    val empty: Command_Status = make(Nil)

    def merge(args: IterableOnce[Command_Status]): Command_Status =
      args.iterator.foldLeft(empty)(_ + _)
  }

  final class Command_Status private(
    val theory_status: Theory_Status.Value,
    private val touched: Boolean,
    private val accepted: Boolean,
    private val warned: Boolean,
    private val failed: Boolean,
    private val canceled: Boolean,
    val forks: Int,
    val runs: Int
  ) extends Theory_Status {
    override def toString: String =
      if (is_empty) "Command_Status.empty"
      else if (failed) "Command_Status(failed)"
      else if (warned) "Command_Status(warned)"
      else "Command_Status(...)"

    def is_empty: Boolean =
      !Theory_Status.initialized(theory_status) &&
      !touched && !accepted && !warned && !failed && !canceled &&
      forks == 0 && runs == 0

    def + (that: Command_Status): Command_Status =
      if (is_empty) that
      else if (that.is_empty) this
      else {
        new Command_Status(
          theory_status = Theory_Status.merge(theory_status, that.theory_status),
          touched = touched || that.touched,
          accepted = accepted || that.accepted,
          warned = warned || that.warned,
          failed = failed || that.failed,
          canceled = canceled || that.canceled,
          forks = forks + that.forks,
          runs = runs + that.runs)
      }

    def maybe_consolidated: Boolean = touched && forks == 0 && runs == 0

    def is_unprocessed: Boolean = accepted && !failed && (!touched || (forks != 0 && runs == 0))
    def is_running: Boolean = runs != 0
    def is_warned: Boolean = warned
    def is_failed: Boolean = failed
    def is_finished: Boolean = !failed && touched && forks == 0 && runs == 0
    def is_canceled: Boolean = canceled
    def is_terminated: Boolean = canceled || touched && forks == 0 && runs == 0
  }


  /* node status */

  object Node_Status {
    val empty: Node_Status = Node_Status()

    def make(
      state: Document.State,
      version: Document.Version,
      name: Document.Node.Name
    ): Node_Status = {
      var unprocessed = 0
      var running = 0
      var warned = 0
      var failed = 0
      var finished = 0
      var canceled = false
      var terminated = true
      var theory_status = Document_Status.Theory_Status.NONE
      for (command <- version.nodes(name).commands.iterator) {
        val status = state.command_status(version, command)

        if (status.is_running) running += 1
        else if (status.is_failed) failed += 1
        else if (status.is_warned) warned += 1
        else if (status.is_finished) finished += 1
        else unprocessed += 1

        if (status.is_canceled) canceled = true
        if (!status.is_terminated) terminated = false

        theory_status = Theory_Status.merge(theory_status, status.theory_status)
      }

      Node_Status(
        suppressed = version.nodes.suppressed(name),
        unprocessed = unprocessed,
        running = running,
        warned = warned,
        failed = failed,
        finished = finished,
        canceled = canceled,
        terminated = terminated,
        theory_status = theory_status)
    }
  }

  sealed case class Node_Status(
    suppressed: Boolean = false,
    unprocessed: Int = 0,
    running: Int = 0,
    warned: Int = 0,
    failed: Int = 0,
    finished: Int = 0,
    canceled: Boolean = false,
    terminated: Boolean = false,
    theory_status: Theory_Status.Value = Theory_Status.NONE
  ) extends Theory_Status {
    def is_empty: Boolean = this == Node_Status.empty

    def ok: Boolean = failed == 0
    def total: Int = unprocessed + running + warned + failed + finished

    def quasi_consolidated: Boolean = !suppressed && !finalized && terminated

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

  object Overall_Timing {
    val empty: Overall_Timing = Overall_Timing()

    def make(
      state: Document.State,
      version: Document.Version,
      name: Document.Node.Name,
      threshold: Time = Time.zero
    ): Overall_Timing = {
      var total = Time.zero
      var command_timings = Map.empty[Command, Time]
      for (command <- version.nodes(name).commands.iterator) {
        val timing = state.command_timing(version, command)
        total += timing.elapsed
        if (timing.is_notable(threshold)) command_timings += (command -> timing.elapsed)
      }
      Overall_Timing(total = total, threshold = threshold, command_timings = command_timings)
    }
  }

  sealed case class Overall_Timing(
    total: Time = Time.zero,
    threshold: Time = Time.zero,
    command_timings: Map[Command, Time] = Map.empty
  ) {
    def command_timing(command: Command): Time =
      command_timings.getOrElse(command, Time.zero)
  }


  /* nodes status */

  enum Overall_Status { case ok, failed, pending }

  object Nodes_Status {
    val empty: Nodes_Status = new Nodes_Status(Map.empty, Document.Nodes.empty)
  }

  final class Nodes_Status private(
    private val rep: Map[Document.Node.Name, Node_Status],
    nodes: Document.Nodes
  ) {
    def is_empty: Boolean = rep.isEmpty
    def defined(name: Document.Node.Name): Boolean = rep.isDefinedAt(name)
    def apply(name: Document.Node.Name): Node_Status = rep(name)
    def get(name: Document.Node.Name): Option[Node_Status] = rep.get(name)

    def present(
      domain: Option[List[Document.Node.Name]] = None
    ): List[(Document.Node.Name, Node_Status)] = {
      for (name <- domain.getOrElse(nodes.topological_order))
        yield name -> get(name).getOrElse(Node_Status.empty)
    }

    def quasi_consolidated(name: Document.Node.Name): Boolean =
      get(name) match {
        case Some(st) => st.quasi_consolidated
        case None => false
      }

    def overall_status(name: Document.Node.Name): Overall_Status =
      get(name) match {
        case Some(st) if st.consolidated =>
          if (st.ok) Overall_Status.ok else Overall_Status.failed
        case _ => Overall_Status.pending
      }

    def update(
      resources: Resources,
      state: Document.State,
      version: Document.Version,
      domain: Option[Set[Document.Node.Name]] = None,
      trim: Boolean = false
    ): (Boolean, Nodes_Status) = {
      val nodes1 = version.nodes
      val update_iterator =
        for {
          name <- domain.getOrElse(nodes1.domain).iterator
          if !Resources.hidden_node(name) && !resources.loaded_theory(name)
          st = Document_Status.Node_Status.make(state, version, name)
          if !defined(name) || apply(name) != st
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

    override def toString: String = {
      var ok = 0
      var failed = 0
      var pending = 0
      var canceled = 0
      for (name <- rep.keysIterator) {
        overall_status(name) match {
          case Overall_Status.ok => ok += 1
          case Overall_Status.failed => failed += 1
          case Overall_Status.pending => pending += 1
        }
        if (apply(name).canceled) canceled += 1
      }
      "Nodes_Status(ok = " + ok + ", failed = " + failed + ", pending = " + pending +
        ", canceled = " + canceled + ")"
    }
  }
}
