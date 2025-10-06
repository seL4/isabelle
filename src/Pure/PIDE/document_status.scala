/*  Title:      Pure/PIDE/document_status.scala
    Author:     Makarius

Document status based on markup information.
*/

package isabelle


import scala.collection.immutable.SortedMap


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


  /* command timings: for pro-forma command with actual commands at offset */

  object Command_Timings {
    type Entry = (Symbol.Offset, Timing)
    val empty: Command_Timings =
      new Command_Timings(SortedMap.empty, Timing.zero)
    def make(args: IterableOnce[Entry]): Command_Timings =
      args.iterator.foldLeft(empty)(_ + _)
    def merge(args: IterableOnce[Command_Timings]): Command_Timings =
      args.iterator.foldLeft(empty)(_ ++ _)
  }

  final class Command_Timings private(
    private val rep: SortedMap[Symbol.Offset, Timing],
    val sum: Timing
  ) {
    def is_empty: Boolean = rep.isEmpty
    def count: Int = rep.size
    def apply(offset: Symbol.Offset): Timing = rep.getOrElse(offset, Timing.zero)
    def iterator: Iterator[(Symbol.Offset, Timing)] = rep.iterator

    def + (entry: Command_Timings.Entry): Command_Timings = {
      val (offset, timing) = entry
      val rep1 = rep + (offset -> (apply(offset) + timing))
      val sum1 = sum + timing
      new Command_Timings(rep1, sum1)
    }

    def ++ (other: Command_Timings): Command_Timings =
      if (rep.isEmpty) other
      else other.rep.foldLeft(this)(_ + _)

    override def hashCode: Int = rep.hashCode
    override def equals(that: Any): Boolean =
      that match {
        case other: Command_Timings => rep == other.rep
        case _ => false
      }
    override def toString: String = rep.mkString("Command_Timings(", ", ", ")")
  }


  /* command status */

  object Command_Status {
    val proper_elements: Markup.Elements =
      Markup.Elements(Markup.ACCEPTED, Markup.FORKED, Markup.JOINED, Markup.RUNNING,
        Markup.FINISHED, Markup.FAILED, Markup.CANCELED)

    val liberal_elements: Markup.Elements =
      proper_elements + Markup.WARNING + Markup.LEGACY + Markup.ERROR

    def make(
      markups: List[Markup] = Nil,
      warned: Boolean = false,
      failed: Boolean = false
    ): Command_Status = {
      var theory_status1 = Theory_Status.NONE
      var touched1 = false
      var accepted1 = false
      var warned1 = warned
      var failed1 = failed
      var canceled1 = false
      var forks1 = 0
      var runs1 = 0
      var timings1 = Command_Timings.empty
      for (markup <- markups) {
        markup.name match {
          case Markup.INITIALIZED =>
            theory_status1 = Theory_Status.merge(theory_status1, Theory_Status.INITIALIZED)
          case Markup.FINALIZED =>
            theory_status1 = Theory_Status.merge(theory_status1, Theory_Status.FINALIZED)
          case Markup.CONSOLIDATING =>
            theory_status1 = Theory_Status.merge(theory_status1, Theory_Status.CONSOLIDATING)
          case Markup.CONSOLIDATED =>
            theory_status1 = Theory_Status.merge(theory_status1, Theory_Status.CONSOLIDATED)
          case Markup.ACCEPTED => accepted1 = true
          case Markup.FORKED => touched1 = true; forks1 += 1
          case Markup.JOINED => forks1 -= 1
          case Markup.RUNNING => touched1 = true; runs1 += 1
          case Markup.FINISHED => runs1 -= 1
          case Markup.WARNING | Markup.LEGACY => warned1 = true
          case Markup.FAILED | Markup.ERROR => failed1 = true
          case Markup.CANCELED => canceled1 = true
          case Markup.TIMING =>
            val props = markup.properties
            val offset = Position.Offset.get(props)
            val timing = Markup.Timing_Properties.get(props)
            timings1 += (offset -> timing)
          case _ =>
        }
      }
      new Command_Status(
        theory_status = theory_status1,
        touched = touched1,
        accepted = accepted1,
        warned = warned1,
        failed = failed1,
        canceled = canceled1,
        forks = forks1,
        runs = runs1,
        timings = timings1)
    }

    val empty: Command_Status = make()

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
    val runs: Int,
    val timings: Command_Timings
  ) extends Theory_Status {
    override def toString: String =
      if (is_empty) "Command_Status.empty"
      else if (failed) "Command_Status(failed)"
      else if (warned) "Command_Status(warned)"
      else "Command_Status(...)"

    def is_empty: Boolean =
      !Theory_Status.initialized(theory_status) &&
      !touched && !accepted && !warned && !failed && !canceled &&
      forks == 0 && runs == 0 && timings.is_empty

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
          runs = runs + that.runs,
          timings = timings ++ that.timings)
      }

    def update(
      markups: List[Markup] = Nil,
      warned: Boolean = false,
      failed: Boolean = false
    ): Command_Status = {
      if (markups.isEmpty) {
        val warned1 = this.warned || warned
        val failed1 = this.failed || failed
        if (this.warned == warned1 && this.failed == failed1) this
        else {
          new Command_Status(
            theory_status = theory_status,
            touched = touched,
            accepted = accepted,
            warned = warned1,
            failed = failed1,
            canceled = canceled,
            forks = forks,
            runs = runs,
            timings = timings)
        }
      }
      else this + Command_Status.make(markups = markups, warned = warned, failed = failed)
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
      name: Document.Node.Name,
      threshold: Time = Time.max
    ): Node_Status = {
      val node = version.nodes(name)

      var theory_status = Document_Status.Theory_Status.NONE
      var unprocessed = 0
      var running = 0
      var warned = 0
      var failed = 0
      var finished = 0
      var canceled = false
      var terminated = true
      var total_timing = Timing.zero
      var max_time = Time.zero
      var command_timings = Map.empty[Command, Command_Timings]

      for (command <- node.commands.iterator) {
        val status = state.command_status(version, command)

        theory_status = Theory_Status.merge(theory_status, status.theory_status)

        if (status.is_running) running += 1
        else if (status.is_failed) failed += 1
        else if (status.is_warned) warned += 1
        else if (status.is_finished) finished += 1
        else unprocessed += 1

        if (status.is_canceled) canceled = true
        if (!status.is_terminated) terminated = false

        val t = status.timings.sum.elapsed
        total_timing += status.timings.sum
        if (t > max_time) max_time = t
        if (t.is_notable(threshold)) command_timings += (command -> status.timings)
      }

      def percent(a: Int, b: Int): Int =
        if (b == 0) 0 else ((a.toDouble / b) * 100).toInt

      val percentage: Int = {
        node.get_theory match {
          case None =>
            if (Theory_Status.consolidated(theory_status)) 100
            else {
              val total = unprocessed + running + warned + failed + finished
              percent(total - unprocessed, total).min(99)
            }
          case Some(command) =>
            val total = command.span.theory_commands
            val processed = state.command_status(version, command).timings.count
            percent(processed, total)
        }
      }

      Node_Status(
        theory_status = theory_status,
        suppressed = version.nodes.suppressed(name),
        unprocessed = unprocessed,
        running = running,
        warned = warned,
        failed = failed,
        finished = finished,
        canceled = canceled,
        terminated = terminated,
        total_timing = total_timing,
        max_time = max_time,
        threshold = threshold,
        command_timings = command_timings,
        percentage)
    }
  }

  sealed case class Node_Status(
    theory_status: Theory_Status.Value = Theory_Status.NONE,
    suppressed: Boolean = false,
    unprocessed: Int = 0,
    running: Int = 0,
    warned: Int = 0,
    failed: Int = 0,
    finished: Int = 0,
    canceled: Boolean = false,
    terminated: Boolean = false,
    total_timing: Timing = Timing.zero,
    max_time: Time = Time.zero,
    threshold: Time = Time.zero,
    command_timings: Map[Command, Command_Timings] = Map.empty,
    percentage: Int = 0
  ) extends Theory_Status {
    def is_empty: Boolean = this == Node_Status.empty

    def ok: Boolean = failed == 0
    def total: Int = unprocessed + running + warned + failed + finished

    def quasi_consolidated: Boolean = !suppressed && !finalized && terminated

    def json: JSON.Object.T =
      JSON.Object("ok" -> ok, "total" -> total, "unprocessed" -> unprocessed,
        "running" -> running, "warned" -> warned, "failed" -> failed, "finished" -> finished,
        "canceled" -> canceled, "consolidated" -> consolidated,
        "percentage" -> percentage)
  }


  /* nodes status */

  enum Overall_Status { case ok, failed, pending }

  object Nodes_Status {
    val empty: Nodes_Status = new Nodes_Status(Map.empty)
  }

  final class Nodes_Status private(private val rep: Map[Document.Node.Name, Node_Status]) {
    def is_empty: Boolean = rep.isEmpty
    def apply(name: Document.Node.Name): Node_Status = rep.getOrElse(name, Node_Status.empty)
    def get(name: Document.Node.Name): Option[Node_Status] = rep.get(name)
    def iterator: Iterator[(Document.Node.Name, Node_Status)] = rep.iterator

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

    def update_node(
      state: Document.State,
      version: Document.Version,
      name: Document.Node.Name,
      threshold: Time = Time.max
    ): Nodes_Status = {
      val node_status = Document_Status.Node_Status.make(state, version, name, threshold = threshold)
      new Nodes_Status(rep + (name -> node_status))
    }

    def update_nodes(
      resources: Resources,
      state: Document.State,
      version: Document.Version,
      threshold: Time = Time.max,
      domain: Option[Set[Document.Node.Name]] = None,
      trim: Boolean = false
    ): Nodes_Status = {
      val domain1 = version.nodes.domain
      val that =
        domain.getOrElse(domain1).iterator.foldLeft(this)(
          { case (a, name) =>
              if (Resources.hidden_node(name) || resources.loaded_theory(name)) a
              else a.update_node(state, version, name, threshold = threshold) })
      if (trim) new Nodes_Status(that.rep -- that.rep.keysIterator.filterNot(domain1))
      else that
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
