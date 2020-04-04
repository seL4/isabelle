/*  Title:      Pure/Concurrent/standard_thread.scala
    Author:     Makarius

Standard thread operations.
*/

package isabelle


import java.util.concurrent.{ThreadPoolExecutor, TimeUnit, LinkedBlockingQueue, ThreadFactory}


object Standard_Thread
{
  /* fork */

  private val counter = Counter.make()

  def make_name(name: String = "", base: String = "thread"): String =
    proper_string(name).getOrElse(base + counter())

  def current_thread_group: ThreadGroup = Thread.currentThread.getThreadGroup

  def fork(
    name: String = "",
    group: ThreadGroup = current_thread_group,
    pri: Int = Thread.NORM_PRIORITY,
    daemon: Boolean = false,
    inherit_locals: Boolean = false)(body: => Unit): Standard_Thread =
  {
    val main = new Runnable { override def run { body } }
    val thread =
      new Standard_Thread(main, name = make_name(name = name), group = group,
        pri = pri, daemon = daemon, inherit_locals = inherit_locals)
    thread.start
    thread
  }


  /* self */

  def self: Standard_Thread =
    Thread.currentThread match {
      case thread: Standard_Thread => thread
      case _ => error("Expected to run on Isabelle/Scala standard thread")
    }

  def uninterruptible[A](body: => A): A = self.uninterruptible(body)


  /* pool */

  lazy val pool: ThreadPoolExecutor =
    {
      val m = Value.Int.unapply(System.getProperty("isabelle.threads", "0")) getOrElse 0
      val n = if (m > 0) m else (Runtime.getRuntime.availableProcessors max 1) min 8
      val executor =
        new ThreadPoolExecutor(n, n, 2500L, TimeUnit.MILLISECONDS, new LinkedBlockingQueue[Runnable])
      executor.setThreadFactory(
        new Standard_Thread(_, name = make_name(base = "worker"), group = current_thread_group))
      executor
    }


  /* delayed events */

  final class Delay private[Standard_Thread](
    first: Boolean, delay: => Time, log: Logger, event: => Unit)
  {
    private var running: Option[Event_Timer.Request] = None

    private def run: Unit =
    {
      val do_run = synchronized {
        if (running.isDefined) { running = None; true } else false
      }
      if (do_run) {
        try { event }
        catch { case exn: Throwable if !Exn.is_interrupt(exn) => log(Exn.message(exn)); throw exn }
      }
    }

    def invoke(): Unit = synchronized
    {
      val new_run =
        running match {
          case Some(request) => if (first) false else { request.cancel; true }
          case None => true
        }
      if (new_run)
        running = Some(Event_Timer.request(Time.now() + delay)(run))
    }

    def revoke(): Unit = synchronized
    {
      running match {
        case Some(request) => request.cancel; running = None
        case None =>
      }
    }

    def postpone(alt_delay: Time): Unit = synchronized
    {
      running match {
        case Some(request) =>
          val alt_time = Time.now() + alt_delay
          if (request.time < alt_time && request.cancel) {
            running = Some(Event_Timer.request(alt_time)(run))
          }
        case None =>
      }
    }
  }

  // delayed event after first invocation
  def delay_first(delay: => Time, log: Logger = No_Logger)(event: => Unit): Delay =
    new Delay(true, delay, log, event)

  // delayed event after last invocation
  def delay_last(delay: => Time, log: Logger = No_Logger)(event: => Unit): Delay =
    new Delay(false, delay, log, event)
}

class Standard_Thread private(
    main: Runnable,
    name: String = "",
    group: ThreadGroup = null,
    pri: Int = Thread.NORM_PRIORITY,
    daemon: Boolean = false,
    inherit_locals: Boolean = false)
  extends Thread(group, null, name, 0L, inherit_locals)
{
  thread =>

  thread.setPriority(pri)
  thread.setDaemon(daemon)

  override def run { main.run() }

  private var interruptible: Boolean = true
  private var interrupt_pending: Boolean = false

  override def interrupt: Unit = synchronized
  {
    if (interruptible) super.interrupt()
    else { interrupt_pending = true }
  }

  def uninterruptible[A](body: => A): A =
  {
    require(Thread.currentThread == thread)

    val interruptible0 = synchronized { val b = interruptible; interruptible = false; b }
    try { body }
    finally {
      synchronized {
        interruptible = interruptible0
        if (interruptible && interrupt_pending) {
          interrupt_pending = false
          super.interrupt()
        }
      }
    }
  }
}
