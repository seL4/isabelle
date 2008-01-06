/*  Title:      jedit/plugin/IsabellePlugin.scala
    ID:         $Id$
    Author:     Makarius

Isabelle/jEdit plugin -- main setup.
*/

package isabelle

import isabelle.IsabelleProcess

import org.gjt.sp.jedit.EditPlugin
import org.gjt.sp.util.Log

import errorlist.DefaultErrorSource
import errorlist.ErrorSource

import scala.collection.mutable.ListBuffer
import java.util.Properties
import java.lang.NumberFormatException


/* Global state */

object IsabellePlugin {
  // unique ids
  @volatile
  private var idCount = 0

  def id() : String = synchronized { idCount += 1; "jedit:" + idCount }

  def idProperties(value: String) : Properties = {
     val props = new Properties
     props.setProperty("id", value)
     props
  }

  def idProperties() : Properties = { idProperties(id()) }


  // the error source
  @volatile
  var errors: DefaultErrorSource = null

  // the Isabelle process
  @volatile
  var isabelle: IsabelleProcess = null


  // result consumers
  type consumer = IsabelleProcess.Result => Boolean
  private var consumers = new ListBuffer[consumer]

  def addConsumer(consumer: consumer) = synchronized { consumers += consumer }

  def addPermanentConsumer(consumer: IsabelleProcess.Result => Unit) = {
    addConsumer(result => { consumer(result); false })
  }

  def delConsumer(consumer: consumer) = synchronized { consumers -= consumer }

  def consume(result: IsabelleProcess.Result) : Unit = {
    synchronized { consumers.elements.toList } foreach (consumer =>
      {
        val finished =
          try { consumer(result) }
          catch { case e: Throwable => Log.log(Log.ERROR, this, e); true }
        if (finished || result == null)
          delConsumer(consumer)
      })
  }
}


/* Main plugin setup */

class IsabellePlugin extends EditPlugin {
  private var thread: Thread = null

  override def start = {
    // error source
    IsabellePlugin.errors = new DefaultErrorSource("isabelle")
    ErrorSource.registerErrorSource(IsabellePlugin.errors)

    IsabellePlugin.addPermanentConsumer (result =>
      if (result != null && result.props != null &&
          (result.kind == IsabelleProcess.Result.Kind.WARNING ||
           result.kind == IsabelleProcess.Result.Kind.ERROR)) {
        val typ =
          if (result.kind == IsabelleProcess.Result.Kind.WARNING) ErrorSource.WARNING
          else ErrorSource.ERROR
        val line = result.props.getProperty(IsabelleProcess.Property.LINE)
        val file = result.props.getProperty(IsabelleProcess.Property.FILE)
        if (line != null && file != null && result.result.length > 0) {
          val msg = result.result.split("\n")
          val err = new DefaultErrorSource.DefaultError(IsabellePlugin.errors,
              typ, file, Integer.parseInt(line) - 1, 0, 0, msg(0))
          for (i <- 1 to msg.length - 1)
            err.addExtraMessage(msg(i))
          IsabellePlugin.errors.addError(err)
        }
      })

    // Isabelle process
    IsabellePlugin.isabelle = new IsabelleProcess(Array("-m", "builtin_browser"), null)
    thread = new Thread (new Runnable {
      def run = {
        var result: IsabelleProcess.Result = null
        do {
          try {
            result = IsabellePlugin.isabelle.results.take.asInstanceOf[IsabelleProcess.Result]
          } catch {
            case _: NullPointerException => null
            case _: InterruptedException => null
          }
          if (result != null) {
            System.err.println(result)   // FIXME
            IsabellePlugin.consume(result)
          }
          if (result.kind == IsabelleProcess.Result.Kind.EXIT) {
            result = null
            IsabellePlugin.consume(null)
          }
        } while (result != null)
      }
    })
    thread.start
  }

  override def stop = {
    IsabellePlugin.isabelle.kill
    thread.interrupt; thread.join; thread = null
    IsabellePlugin.isabelle = null

    ErrorSource.unregisterErrorSource(IsabellePlugin.errors)
    IsabellePlugin.errors = null
  }
}

