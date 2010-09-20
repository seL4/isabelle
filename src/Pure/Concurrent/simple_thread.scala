/*  Title:      Pure/Concurrent/simple_thread.scala
    Author:     Makarius

Simplified thread operations.
*/

package isabelle


import java.lang.Thread

import scala.actors.Actor


object Simple_Thread
{
  /* plain thread */

  def fork(name: String, daemon: Boolean = false)(body: => Unit): Thread =
  {
    val thread = new Thread(name) { override def run = body }
    thread.setDaemon(daemon)
    thread.start
    thread
  }


  /* thread as actor */

  def actor(name: String, daemon: Boolean = false)(body: => Unit): (Thread, Actor) =
  {
    val actor = Future.promise[Actor]
    val thread = fork(name, daemon) { actor.fulfill(Actor.self); body }
    (thread, actor.join)
  }
}

