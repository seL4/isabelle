/*  Title:      Pure/Concurrent/event_timer.scala
    Author:     Makarius

Initiate event after given point in time.

Note: events are run as synchronized action within a dedicated thread
and should finish quickly without further ado.
*/

package isabelle


import java.util.{Timer, TimerTask, Date => JDate}


object Event_Timer {
  private lazy val event_timer = new Timer("event_timer", true)

  final class Request private[Event_Timer](
    val time: Time,
    val repeat: Option[Time],
    task: TimerTask
  ) {
    def cancel(): Boolean = task.cancel()
  }

  def request(
    time: Time,
    repeat: Option[Time] = None,
    log: Logger = new Console_Logger()
  )(event: => Unit): Request = {
    val task =
      new TimerTask {
        def run(): Unit =
          Exn.capture_trace(log(_, kind = Output.Kind.error_message)) { event }
      }
    repeat match {
      case None => event_timer.schedule(task, new JDate(time.ms))
      case Some(rep) => event_timer.schedule(task, new JDate(time.ms), rep.ms)
    }
    new Request(time, repeat, task)
  }
}
