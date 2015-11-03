/*  Title:      Pure/Concurrent/standard_thread.scala
    Module:     PIDE
    Author:     Makarius

Standard thread operations.
*/

package isabelle


import java.lang.Thread
import java.util.concurrent.{Callable, Future => JFuture, ThreadPoolExecutor,
  TimeUnit, LinkedBlockingQueue}


object Standard_Thread
{
  /* plain thread */

  def fork(name: String = "", daemon: Boolean = false)(body: => Unit): Thread =
  {
    val thread =
      if (name == null || name == "") new Thread() { override def run = body }
      else new Thread(name) { override def run = body }
    thread.setDaemon(daemon)
    thread.start
    thread
  }


  /* thread pool */

  lazy val pool: ThreadPoolExecutor =
    {
      val m = Properties.Value.Int.unapply(System.getProperty("isabelle.threads", "0")) getOrElse 0
      val n = if (m > 0) m else (Runtime.getRuntime.availableProcessors max 1) min 8
      new ThreadPoolExecutor(n, n, 2500L, TimeUnit.MILLISECONDS, new LinkedBlockingQueue[Runnable])
    }

  def submit_task[A](body: => A): JFuture[A] =
    pool.submit(new Callable[A] { def call = body })


  /* delayed events */

  final class Delay private [Standard_Thread](
    first: Boolean, delay: => Time, cancel: () => Unit, event: => Unit)
  {
    private var running: Option[Event_Timer.Request] = None

    private def run: Unit =
    {
      val do_run = synchronized {
        if (running.isDefined) { running = None; true } else false
      }
      if (do_run) event
    }

    def invoke(): Unit = synchronized
    {
      val new_run =
        running match {
          case Some(request) => if (first) false else { request.cancel; cancel(); true }
          case None => cancel(); true
        }
      if (new_run)
        running = Some(Event_Timer.request(Time.now() + delay)(run))
    }

    def revoke(): Unit = synchronized
    {
      running match {
        case Some(request) => request.cancel; cancel(); running = None
        case None => cancel()
      }
    }

    def postpone(alt_delay: Time): Unit = synchronized
    {
      running match {
        case Some(request) =>
          val alt_time = Time.now() + alt_delay
          if (request.time < alt_time && request.cancel) {
            cancel()
            running = Some(Event_Timer.request(alt_time)(run))
          }
          else cancel()
        case None => cancel()
      }
    }
  }

  // delayed event after first invocation
  def delay_first(delay: => Time, cancel: () => Unit = () => ())(event: => Unit): Delay =
    new Delay(true, delay, cancel, event)

  // delayed event after last invocation
  def delay_last(delay: => Time, cancel: () => Unit = () => ())(event: => Unit): Delay =
    new Delay(false, delay, cancel, event)
}
