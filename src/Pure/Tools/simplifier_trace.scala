/*  Title:      Pure/Tools/simplifier_trace.scala
    Author:     Lars Hupel

Interactive Simplifier trace.
*/

package isabelle

import scala.actors.Actor._
import scala.annotation.tailrec
import scala.collection.immutable.SortedMap


object Simplifier_Trace
{

  import Markup.Simp_Trace_Item


  /* replies to the prover */

  case class Answer private[Simplifier_Trace](val name: String, val string: String)

  object Answer
  {

    object step
    {
      val skip = Answer("skip", "Skip")
      val continue = Answer("continue", "Continue")
      val continue_trace = Answer("continue_trace", "Continue (with full trace)")
      val continue_passive = Answer("continue_passive", "Continue (without asking)")
      val continue_disable = Answer("continue_disable", "Continue (without any trace)")

      val default = skip
      val all = List(continue, continue_trace, continue_passive, continue_disable, skip)
    }

    object hint_fail
    {
      val exit = Answer("exit", "Exit")
      val redo = Answer("redo", "Redo")

      val default = exit
      val all = List(redo, exit)
    }

  }

  val all_answers = Answer.step.all ++ Answer.hint_fail.all


  /* GUI interaction */

  case object Event


  /* manager actor */

  private case class Handle_Results(session: Session, id: Document_ID.Command, results: Command.Results)
  private case class Generate_Trace(results: Command.Results)
  private case class Cancel(serial: Long)
  private object Clear_Memory
  private object Stop
  case class Reply(session: Session, serial: Long, answer: Answer)

  case class Question(data: Simp_Trace_Item.Data, answers: List[Answer], default_answer: Answer)

  case class Context(
    last_serial: Long = 0L,
    questions: SortedMap[Long, Question] = SortedMap.empty
  )
  {

    def +(q: Question): Context =
      copy(questions = questions + ((q.data.serial, q)))

    def -(s: Long): Context =
      copy(questions = questions - s)

    def with_serial(s: Long): Context =
      copy(last_serial = Math.max(last_serial, s))

  }

  case class Trace(entries: List[Simp_Trace_Item.Data])

  case class Index(text: String, content: XML.Body)

  object Index
  {
    def of_data(data: Simp_Trace_Item.Data): Index =
      Index(data.text, data.content)
  }

  def handle_results(session: Session, id: Document_ID.Command, results: Command.Results): Context =
    (manager !? Handle_Results(session, id, results)).asInstanceOf[Context]

  def generate_trace(results: Command.Results): Trace =
    (manager !? Generate_Trace(results)).asInstanceOf[Trace]

  def clear_memory() =
    manager ! Clear_Memory

  def send_reply(session: Session, serial: Long, answer: Answer) =
    manager ! Reply(session, serial, answer)

  private val manager = actor {
    var contexts = Map.empty[Document_ID.Command, Context]

    var memory_children = Map.empty[Long, Set[Long]]
    var memory = Map.empty[Index, Answer]

    def find_question(serial: Long): Option[(Document_ID.Command, Question)] =
      contexts collectFirst {
        case (id, context) if context.questions contains serial =>
          (id, context.questions(serial))
      }

    def do_cancel(serial: Long, id: Document_ID.Command)
    {
      // To save memory, we could try to remove empty contexts at this point.
      // However, if a new serial gets attached to the same command_id after we deleted
      // its context, its last_serial counter will start at 0 again, and we'll think the
      // old serials are actually new
      contexts += (id -> (contexts(id) - serial))
    }

    def do_reply(session: Session, serial: Long, answer: Answer)
    {
      session.protocol_command("Document.simp_trace_reply", Properties.Value.Long(serial), answer.name)
    }

    loop {
      react {
        case Handle_Results(session, id, results) =>
          var new_context = contexts.getOrElse(id, Context())
          var new_serial = new_context.last_serial

          for ((serial, result) <- results.entries if serial > new_context.last_serial)
          {
            result match {
              case Simp_Trace_Item(markup, data) =>
                import Simp_Trace_Item._

                memory_children += (data.parent -> (memory_children.getOrElse(data.parent, Set.empty) + serial))

                markup match {

                  case STEP =>
                    val index = Index.of_data(data)
                    memory.get(index) match {
                      case Some(answer) if data.memory =>
                        do_reply(session, serial, answer)
                      case _ =>
                        new_context += Question(data, Answer.step.all, Answer.step.default)
                    }

                  case HINT =>
                    data.props match {
                      case Markup.Success(false) =>
                        results.get(data.parent) match {
                          case Some(Simp_Trace_Item(STEP, _)) =>
                            new_context += Question(data, Answer.hint_fail.all, Answer.hint_fail.default)
                          case _ =>
                            // unknown, better send a default reply
                            do_reply(session, data.serial, Answer.hint_fail.default)
                        }
                      case _ =>
                    }

                  case IGNORE =>
                    // At this point, we know that the parent of this 'IGNORE' entry is a 'STEP'
                    // entry, and that that 'STEP' entry is about to be replayed. Hence, we need
                    // to selectively purge the replies which have been memorized, going down from
                    // the parent to all leaves.

                    @tailrec
                    def purge(queue: Vector[Long]): Unit =
                      queue match {
                        case s +: rest =>
                          for (Simp_Trace_Item(STEP, data) <- results.get(s))
                            memory -= Index.of_data(data)
                          val children = memory_children.getOrElse(s, Set.empty)
                          memory_children -= s
                          purge(rest ++ children.toVector)
                        case _ =>
                      }

                    purge(Vector(data.parent))

                  case _ =>
                }

              case _ =>
            }

            new_serial = serial
          }

          new_context = new_context.with_serial(new_serial)
          contexts += (id -> new_context)
          reply(new_context)

        case Generate_Trace(results) =>
          // Since there are potentially lots of trace messages, we do not cache them here again.
          // Instead, everytime the trace is being requested, we re-assemble it based on the
          // current results.

          val items =
            for { (_, Simp_Trace_Item(_, data)) <- results.entries }
              yield data

          reply(Trace(items.toList))

        case Cancel(serial) =>
          find_question(serial) match {
            case Some((id, _)) =>
              do_cancel(serial, id)
            case None =>
              System.err.println("handle_cancel: unknown serial " + serial)
          }

        case Clear_Memory =>
          memory_children = Map.empty
          memory = Map.empty

        case Stop =>
          contexts = Map.empty
          exit("Simplifier_Trace: manager actor stopped")

        case Reply(session, serial, answer) =>
          find_question(serial) match {
            case Some((id, Question(data, _, _))) =>
              if (data.markup == Markup.Simp_Trace_Item.STEP && data.memory)
              {
                val index = Index.of_data(data)
                memory += (index -> answer)
              }
              do_cancel(serial, id)
            case None =>
              System.err.println("send_reply: unknown serial " + serial)
          }

          do_reply(session, serial, answer)
          session.trace_events.event(Event)

        case bad =>
          System.err.println("context_manager: bad message " + bad)
      }
    }
  }


  /* protocol handler */

  class Handler extends Session.Protocol_Handler
  {
    private def cancel(
      prover: Session.Prover, msg: Isabelle_Process.Protocol_Output): Boolean =
      msg.properties match {
        case Markup.Cancel_Simp_Trace(serial) =>
          manager ! Cancel(serial)
          true
        case _ =>
          false
      }

    override def stop(prover: Session.Prover) =
    {
      manager ! Clear_Memory
      manager ! Stop
    }

    val functions = Map(
      Markup.CANCEL_SIMP_TRACE -> cancel _)
  }

}
