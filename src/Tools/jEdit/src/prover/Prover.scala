/*
 * Higher-level prover communication
 *
 * @author Johannes Hölzl, TU Munich
 * @author Fabian Immler, TU Munich
 */

package isabelle.prover

import scala.collection.mutable.{ HashMap, HashSet }

import java.util.Properties

import javax.swing.SwingUtilities

import isabelle.proofdocument.{ ProofDocument, Text, Token }
import isabelle.IsabelleProcess.Result
import isabelle.YXML.parse_failsafe
import isabelle.XML.{ Elem, Tree }
import isabelle.Symbol.Interpretation
import isabelle.IsabelleSyntax.{ encode_properties, encode_string }

import isabelle.utils.EventSource

import Command.Phase

class Prover() {
  val converter = new Interpretation()

  private var _logic = "HOL"
  private var process = null : IsabelleProcess
  private var commands = new HashMap[String, Command]
  
  val command_decls = new HashSet[String]
  val keyword_decls = new HashSet[String]
  private var initialized = false
    
  val activated = new EventSource[Unit]
  val commandInfo = new EventSource[CommandChangeInfo]
  val outputInfo = new EventSource[String]
  val allInfo = new EventSource[Result]
  var document = null : Document

  def fireChange(c : Command) =
    inUIThread(() => commandInfo.fire(new CommandChangeInfo(c)))

  var workerThread = new Thread("isabelle.Prover: worker") {
    override def run() : Unit = {
      while (true) {
        val r = process.get_result
        
        val id = if (r.props != null) r.props.getProperty("id") else null
        val st = if (id != null) commands.getOrElse(id, null) else null
        
        if (r.kind == IsabelleProcess.Kind.EXIT)
          return
        else if (r.kind == IsabelleProcess.Kind.STDOUT 
                 || r.kind == IsabelleProcess.Kind.STDIN)
          inUIThread(() => outputInfo.fire(r.result))
        else if (r.kind == IsabelleProcess.Kind.WRITELN && !initialized) {
          initialized = true
          inUIThread(() => 
            if (document != null) {
              document.activate()
              activated.fire(())
            }
          )
        }
        else {
          val tree = parse_failsafe(converter.decode(r.result))
          if (st == null || (st.phase != Phase.REMOVED && st.phase != Phase.REMOVE))
          tree match {
            //handle all kinds of status messages here
            case Elem("message", List(("class","status")), elems) =>
              elems map (elem => elem match{

                  // catch command_start and keyword declarations
                  case Elem("command_decl", List(("name", name), ("kind", _)), _) =>
                    command_decls.addEntry(name)
                  case Elem("keyword_decl", List(("name", name)), _) =>
                    keyword_decls.addEntry(name)

                  // expecting markups here
                  case Elem(kind, List(("offset", offset),
                                       ("end_offset", end_offset),
                                       ("id", id)), List()) =>
                    val begin = Int.unbox(java.lang.Integer.valueOf(offset)) - 1
                    val end = Int.unbox(java.lang.Integer.valueOf(end_offset)) - 1

                    val command =
                      // outer syntax: no id in props
                      if(st == null) commands.getOrElse(id, null)
                      // inner syntax: id from props
                      else st
                    command.root_node.insert(command.node_from(kind, begin, end))

                  // Phase changed
                  case Elem("finished", _, _) =>
                    st.phase = Phase.FINISHED
                    fireChange(st)
                  case Elem("unprocessed", _, _) =>
                    st.phase = Phase.UNPROCESSED
                    fireChange(st)
                  case Elem("failed", _, _) =>
                    st.phase = Phase.FAILED
                    fireChange(st)
                  case Elem("removed", _, _) =>
                    document.prover.commands.removeKey(st.idString)
                    st.phase = Phase.REMOVED
                    fireChange(st)
                  case _ =>
                }) 
            case _ =>
              if (st != null)
              handleResult(st, r, tree)
          }
        }
        
      }
    }
  }
  
  def handleResult(st : Command, r : Result, tree : XML.Tree) {
    //TODO: this is just for testing
    allInfo.fire(r)
    
    r.kind match {
      case IsabelleProcess.Kind.ERROR => 
        if (st.phase != Phase.REMOVED && st.phase != Phase.REMOVE)
          st.phase = Phase.FAILED
        st.addResult(tree)
        fireChange(st)
        
      case IsabelleProcess.Kind.WRITELN =>
        st.addResult(tree)
        fireChange(st)
        
      case IsabelleProcess.Kind.PRIORITY =>
        st.addResult(tree)
        fireChange(st)

      case IsabelleProcess.Kind.WARNING =>
        st.addResult(tree)
        fireChange(st)
              
      case IsabelleProcess.Kind.STATUS =>
        System.err.println("handleResult - Ignored: " + tree)

      case _ =>
    }
  }
  
  def logic = _logic
  
  def start(logic : String) {
    if (logic != null)
      _logic = logic
    process = new IsabelleProcess("-m", "xsymbols", _logic)
    workerThread.start
  }

  def stop() {
    process.kill
  }
  
  private def inUIThread(runnable : () => Unit) {
    SwingUtilities invokeAndWait new Runnable() {
      override def run() { runnable () }
    }
  }
  
  def setDocument(text : Text, path : String) {
    this.document = new Document(text, this)
    process.ML("ThyLoad.add_path " + encode_string(path))

    document.structuralChanges.add(changes => {
      for (cmd <- changes.removedCommands) remove(cmd)
      for (cmd <- changes.addedCommands) send(cmd)
    })
    if (initialized) {
      document.activate()
      activated.fire(())
    }
  }
  
  private def send(cmd : Command) {
    commands.put(cmd.idString, cmd)
    
    val props = new Properties()
    props.setProperty("id", cmd.idString)
    props.setProperty("offset", Integer.toString(1))

    val content = converter.encode(document.getContent(cmd))
    process.output_sync("Isar.command " 
                        + encode_properties(props)
                        + " "
                        + encode_string(content))
    
    process.output_sync("Isar.insert "
                        + encode_string(if (cmd.previous == null) "" 
                                        else cmd.previous.idString)
                        + " "
                        + encode_string(cmd.idString))
    
    cmd.phase = Phase.UNPROCESSED
  }
  
  def remove(cmd : Command) {
    cmd.phase = Phase.REMOVE
    process.output_sync("Isar.remove " + encode_string(cmd.idString))
  }
}