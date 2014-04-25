/*  Title:      Pure/Concurrent/simple_thread.scala
    Module:     PIDE
    Author:     Makarius

Simplified thread operations.
*/

package isabelle


import java.lang.Thread
import java.util.concurrent.{Callable, Future => JFuture}

import scala.collection.parallel.ForkJoinTasks


object Simple_Thread
{
  /* pending interrupts */

  def interrupted_exception(): Unit =
    if (Thread.interrupted()) throw Exn.Interrupt()


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


  /* future result via thread */

  def future[A](name: String = "", daemon: Boolean = false)(body: => A): (Thread, Future[A]) =
  {
    val result = Future.promise[A]
    val thread = fork(name, daemon) { result.fulfill_result(Exn.capture(body)) }
    (thread, result)
  }


  /* thread pool */

  lazy val default_pool = ForkJoinTasks.defaultForkJoinPool

  def submit_task[A](body: => A): JFuture[A] =
    default_pool.submit(new Callable[A] { def call = body })
}

