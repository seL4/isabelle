/*  Title:      jedit/plugin/IsabellePlugin.scala
    ID:         $Id$
    Author:     Makarius

Isabelle/jEdit plugin -- main setup.
*/

package isabelle.jedit

import org.gjt.sp.jedit.EditPlugin
import org.gjt.sp.util.Log

import errorlist.DefaultErrorSource
import errorlist.ErrorSource

import java.util.Properties
import java.lang.NumberFormatException

import scala.collection.mutable.ListBuffer
import scala.io.Source


/* Global state */

object IsabellePlugin {
  // unique ids
  @volatile
  private var idCount = 0

  def id() : String = synchronized { idCount += 1; "jedit:" + idCount }

  def idProperties(value: String) : Properties = {
     val props = new Properties
     props.setProperty(Markup.ID, value)
     props
  }

  def idProperties() : Properties = { idProperties(id()) }


  // the error source
  @volatile
  var errors: DefaultErrorSource = null

  // the Isabelle process
  @volatile
  var isabelle: IsabelleProcess = null


  // result content
  def result_content(result: IsabelleProcess.Result) =
    XML.content(isabelle.result_tree(result)).mkString("")


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
          (result.kind == IsabelleProcess.Kind.WARNING ||
           result.kind == IsabelleProcess.Kind.ERROR)) {
        val typ =
          if (result.kind == IsabelleProcess.Kind.WARNING) ErrorSource.WARNING
          else ErrorSource.ERROR
        (Position.line_of(result.props), Position.file_of(result.props)) match {
          case (Some(line), Some(file)) =>
            val content = IsabellePlugin.result_content(result)
            if (content.length > 0) {
              val lines = Source.fromString(content).getLines
              val err = new DefaultErrorSource.DefaultError(IsabellePlugin.errors,
                  typ, file, line - 1, 0, 0, lines.next)
              for (msg <- lines) err.addExtraMessage(msg)
              IsabellePlugin.errors.addError(err)
            }
          case _ =>
        }
      })


    // Isabelle process
    IsabellePlugin.isabelle =
      new IsabelleProcess("-mno_brackets", "-mno_type_brackets", "-mxsymbols")
    thread = new Thread (new Runnable {
      def run = {
        var result: IsabelleProcess.Result = null
        do {
          try {
            result = IsabellePlugin.isabelle.results.take
          }
          catch {
            case _: NullPointerException => result = null
            case _: InterruptedException => result = null
          }
          if (result != null) {
            System.err.println(result)   // FIXME
            IsabellePlugin.consume(result)
          }
          if (result.kind == IsabelleProcess.Kind.EXIT) {
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
