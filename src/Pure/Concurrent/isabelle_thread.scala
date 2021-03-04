/*  Title:      Pure/Concurrent/isabelle_thread.scala
    Author:     Makarius

Isabelle-specific thread management.
*/

package isabelle


import java.util.concurrent.{ThreadPoolExecutor, TimeUnit, LinkedBlockingQueue}


object Isabelle_Thread
{
  /* self-thread */

  def self: Isabelle_Thread =
    Thread.currentThread match {
      case thread: Isabelle_Thread => thread
      case thread => error("Isabelle-specific thread required: " + thread)
    }

  def check_self: Boolean =
    Thread.currentThread.isInstanceOf[Isabelle_Thread]


  /* create threads */

  private val counter = Counter.make()

  def make_name(name: String = "", base: String = "thread"): String =
  {
    val prefix = "Isabelle."
    val suffix = if (name.nonEmpty) name else base + counter()
    if (suffix.startsWith(prefix)) suffix else prefix + suffix
  }

  def current_thread_group: ThreadGroup = Thread.currentThread.getThreadGroup

  lazy val worker_thread_group: ThreadGroup =
    new ThreadGroup(current_thread_group, "Isabelle worker")

  def create(
    main: Runnable,
    name: String = "",
    group: ThreadGroup = current_thread_group,
    pri: Int = Thread.NORM_PRIORITY,
    daemon: Boolean = false,
    inherit_locals: Boolean = false): Isabelle_Thread =
  {
    new Isabelle_Thread(main, name = make_name(name = name), group = group,
      pri = pri, daemon = daemon, inherit_locals = inherit_locals)
  }

  def fork(
    name: String = "",
    group: ThreadGroup = current_thread_group,
    pri: Int = Thread.NORM_PRIORITY,
    daemon: Boolean = false,
    inherit_locals: Boolean = false,
    uninterruptible: Boolean = false)(body: => Unit): Isabelle_Thread =
  {
    val main: Runnable =
      if (uninterruptible) { () => Isabelle_Thread.uninterruptible { body } }
      else { () => body }
    val thread =
      create(main, name = name, group = group, pri = pri,
        daemon = daemon, inherit_locals = inherit_locals)
    thread.start
    thread
  }


  /* thread pool */

  def max_threads(): Int =
  {
    val m = Value.Int.unapply(System.getProperty("isabelle.threads", "0")) getOrElse 0
    if (m > 0) m else (Runtime.getRuntime.availableProcessors max 1) min 8
  }

  lazy val pool: ThreadPoolExecutor =
  {
    val n = max_threads()
    val executor =
      new ThreadPoolExecutor(n, n, 2500L, TimeUnit.MILLISECONDS, new LinkedBlockingQueue[Runnable])
    executor.setThreadFactory(
      create(_, name = make_name(base = "worker"), group = worker_thread_group))
    executor
  }


  /* interrupt handlers */

  object Interrupt_Handler
  {
    def apply(handle: Isabelle_Thread => Unit, name: String = "handler"): Interrupt_Handler =
      new Interrupt_Handler(handle, name)

    val interruptible: Interrupt_Handler =
      Interrupt_Handler(_.raise_interrupt, name = "interruptible")

    val uninterruptible: Interrupt_Handler =
      Interrupt_Handler(_.postpone_interrupt, name = "uninterruptible")
  }

  class Interrupt_Handler private(handle: Isabelle_Thread => Unit, name: String)
    extends Function[Isabelle_Thread, Unit]
  {
    def apply(thread: Isabelle_Thread): Unit = handle(thread)
    override def toString: String = name
  }

  def interrupt_handler[A](handler: Interrupt_Handler)(body: => A): A =
    if (handler == null) body
    else self.interrupt_handler(handler)(body)

  def interrupt_handler[A](handle: Isabelle_Thread => Unit)(body: => A): A =
    self.interrupt_handler(Interrupt_Handler(handle))(body)

  def interruptible[A](body: => A): A =
    interrupt_handler(Interrupt_Handler.interruptible)(body)

  def uninterruptible[A](body: => A): A =
    interrupt_handler(Interrupt_Handler.uninterruptible)(body)

  def try_uninterruptible[A](body: => A): A =
    if (check_self) interrupt_handler(Interrupt_Handler.uninterruptible)(body)
    else body
}

class Isabelle_Thread private(main: Runnable, name: String, group: ThreadGroup,
    pri: Int, daemon: Boolean, inherit_locals: Boolean)
  extends Thread(group, null, name, 0L, inherit_locals)
{
  thread =>

  thread.setPriority(pri)
  thread.setDaemon(daemon)

  override def run: Unit = main.run()

  def is_self: Boolean = Thread.currentThread == thread


  /* interrupt state */

  // synchronized, with concurrent changes
  private var interrupt_postponed: Boolean = false

  def clear_interrupt: Boolean = synchronized
  {
    val was_interrupted = isInterrupted || interrupt_postponed
    Exn.Interrupt.dispose()
    interrupt_postponed = false
    was_interrupted
  }

  def raise_interrupt: Unit = synchronized
  {
    interrupt_postponed = false
    super.interrupt()
  }

  def postpone_interrupt: Unit = synchronized
  {
    interrupt_postponed = true
    Exn.Interrupt.dispose()
  }


  /* interrupt handler */

  // non-synchronized, only changed on self-thread
  @volatile private var handler = Isabelle_Thread.Interrupt_Handler.interruptible

  override def interrupt(): Unit = handler(thread)

  def interrupt_handler[A](new_handler: Isabelle_Thread.Interrupt_Handler)(body: => A): A =
    if (new_handler == null) body
    else {
      require(is_self, "interrupt handler on other thread")

      val old_handler = handler
      handler = new_handler
      try {
        if (clear_interrupt) interrupt()
        body
      }
      finally {
        handler = old_handler
        if (clear_interrupt) interrupt()
      }
    }
}
