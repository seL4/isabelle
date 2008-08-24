/*  Title:      lib/jedit/plugin/isabelle_plugin.scala
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



/** global state **/

object IsabellePlugin {

  /* Isabelle process */

  var isabelle: IsabelleProcess = null

  def result_content(result: IsabelleProcess.Result) =
    XML.content(isabelle.decode_result(result)).mkString("")


  /* unique ids */

  private var id_count: BigInt = 0

  def id() : String = synchronized { id_count += 1; "jedit:" + id_count }

  def id_properties(value: String) : Properties = {
     val props = new Properties
     props.setProperty(Markup.ID, value)
     props
  }

  def id_properties() : Properties = { id_properties(id()) }


  /* result consumers */

  type Consumer = IsabelleProcess.Result => Boolean
  private var consumers = new ListBuffer[Consumer]

  def add_consumer(consumer: Consumer) = synchronized { consumers += consumer }

  def add_permanent_consumer(consumer: IsabelleProcess.Result => Unit) = {
    add_consumer(result => { consumer(result); false })
  }

  def del_consumer(consumer: Consumer) = synchronized { consumers -= consumer }

  private def consume(result: IsabelleProcess.Result) = {
    synchronized { consumers.elements.toList } foreach (consumer =>
      {
        if (result != null && result.is_control) Log.log(Log.DEBUG, result, null)
        val finished =
          try { consumer(result) }
          catch { case e: Throwable => Log.log(Log.ERROR, result, e); true }
        if (finished || result == null) del_consumer(consumer)
      })
  }

  class ConsumerThread extends Thread {
    override def run = {
      var finished = false
      while (!finished) {
        val result =
          try { IsabellePlugin.isabelle.get_result() }
          catch { case _: NullPointerException => null }

        if (result != null) {
          consume(result)
          if (result.kind == IsabelleProcess.Kind.EXIT) {
            consume(null)
            finished = true
          }
        }
        else finished = true
      }
    }
  }

}


/* Main plugin setup */

class IsabellePlugin extends EditPlugin {

  import IsabellePlugin._

  val errors = new DefaultErrorSource("isabelle")
  val consumer_thread = new ConsumerThread


  override def start = {

    /* error source */

    ErrorSource.registerErrorSource(errors)

    add_permanent_consumer (result =>
      if (result != null &&
          (result.kind == IsabelleProcess.Kind.WARNING ||
           result.kind == IsabelleProcess.Kind.ERROR)) {
        (Position.line_of(result.props), Position.file_of(result.props)) match {
          case (Some(line), Some(file)) =>
            val typ =
              if (result.kind == IsabelleProcess.Kind.WARNING) ErrorSource.WARNING
              else ErrorSource.ERROR
            val content = result_content(result)
            if (content.length > 0) {
              val lines = Source.fromString(content).getLines
              val err = new DefaultErrorSource.DefaultError(errors,
                  typ, file, line - 1, 0, 0, lines.next)
              for (msg <- lines) err.addExtraMessage(msg)
              errors.addError(err)
            }
          case _ =>
        }
      })


    /* Isabelle process */

    isabelle = new IsabelleProcess("-mno_brackets", "-mno_type_brackets", "-mxsymbols")
    consumer_thread.start

  }


  override def stop = {
    isabelle.kill
    consumer_thread.join
    ErrorSource.unregisterErrorSource(errors)
  }

}
