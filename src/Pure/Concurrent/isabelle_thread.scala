/*  Title:      Pure/Concurrent/isabelle_thread.scala
    Author:     Makarius

Isabelle-specific thread management.
*/

package isabelle


import java.util.concurrent.{ThreadPoolExecutor, TimeUnit, LinkedBlockingQueue, ThreadFactory}


object Isabelle_Thread
{
  /* fork */

  private val counter = Counter.make()

  def make_name(name: String = "", base: String = "thread"): String =
    "Isabelle." + proper_string(name).getOrElse(base + counter())

  def current_thread_group: ThreadGroup = Thread.currentThread.getThreadGroup

  def fork(
    name: String = "",
    group: ThreadGroup = current_thread_group,
    pri: Int = Thread.NORM_PRIORITY,
    daemon: Boolean = false,
    inherit_locals: Boolean = false,
    uninterruptible: Boolean = false)(body: => Unit): Isabelle_Thread =
  {
    val main =
      if (uninterruptible) new Runnable { override def run { Isabelle_Thread.uninterruptible { body } } }
      else new Runnable { override def run { body } }
    val thread =
      new Isabelle_Thread(main, name = make_name(name = name), group = group,
        pri = pri, daemon = daemon, inherit_locals = inherit_locals)
    thread.start
    thread
  }


  /* self */

  def self: Isabelle_Thread =
    Thread.currentThread match {
      case thread: Isabelle_Thread => thread
      case _ => error("Isabelle-specific thread required")
    }


  /* interrupts */

  type Interrupt_Handler = Isabelle_Thread => Unit

  def interrupt_handler[A](handler: Interrupt_Handler)(body: => A): A =
    self.interrupt_handler(handler)(body)

  def interruptible[A](body: => A): A = interrupt_handler(_.raise_interrupt)(body)
  def uninterruptible[A](body: => A): A = interrupt_handler(_.postpone_interrupt)(body)


  /* pool */

  lazy val pool: ThreadPoolExecutor =
    {
      val m = Value.Int.unapply(System.getProperty("isabelle.threads", "0")) getOrElse 0
      val n = if (m > 0) m else (Runtime.getRuntime.availableProcessors max 1) min 8
      val executor =
        new ThreadPoolExecutor(n, n, 2500L, TimeUnit.MILLISECONDS, new LinkedBlockingQueue[Runnable])
      executor.setThreadFactory(
        new Isabelle_Thread(_, name = make_name(base = "worker"), group = current_thread_group))
      executor
    }


  /* delayed events */

  final class Delay private[Isabelle_Thread](
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

class Isabelle_Thread private(
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


  /* interrupt state */

  private var interrupt_pending: Boolean = false

  def raise_interrupt: Unit = synchronized
  {
    interrupt_pending = false
    super.interrupt()
  }

  def postpone_interrupt: Unit = synchronized
  {
    interrupt_pending = true
    Exn.Interrupt.dispose()
  }


  /* interrupt handler */

  private var handler: Isabelle_Thread.Interrupt_Handler = (_.raise_interrupt)

  override def interrupt: Unit = (synchronized { handler })(thread)

  def interrupt_handler[A](new_handler: Isabelle_Thread.Interrupt_Handler)(body: => A): A =
  {
    require(Thread.currentThread == thread)

    val old_handler = handler
    handler = new_handler
    try { body }
    finally {
      synchronized {
        handler = old_handler
        if (isInterrupted || interrupt_pending) thread.interrupt
      }
      Exn.Interrupt.expose()
    }
  }
}
