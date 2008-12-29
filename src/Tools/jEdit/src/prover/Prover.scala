/*
 * Higher-level prover communication
 *
 * @author Johannes Hölzl, TU Munich
 * @author Fabian Immler, TU Munich
 * @author Makarius
 */

package isabelle.prover


import java.util.Properties
import javax.swing.SwingUtilities

import scala.collection.mutable.{HashMap, HashSet}

import isabelle.proofdocument.{ProofDocument, Text, Token}
import isabelle.{Symbol, IsabelleSyntax}
import isabelle.utils.EventSource

import Command.Phase


class Prover(isabelle_system: IsabelleSystem, isabelle_symbols: Symbol.Interpretation)
{
  private var _logic = isabelle_system.getenv_strict("ISABELLE_LOGIC")
  private var process: Isar = null
  private var commands = new HashMap[String, Command]

  val command_decls = new HashSet[String]
  val keyword_decls = new HashSet[String]
  private var initialized = false

  val activated = new EventSource[Unit]
  val commandInfo = new EventSource[Command]
  val outputInfo = new EventSource[String]
  var document: Document = null


  def swing(body: => Unit) =
    SwingUtilities.invokeAndWait(new Runnable { def run = body })

  def swing_async(body: => Unit) =
    SwingUtilities.invokeLater(new Runnable { def run = body })


  def fireChange(c: Command) = swing { commandInfo.fire(c) }

  private def handle_result(r: IsabelleProcess.Result) = {
    val id = if (r.props != null) r.props.getProperty(Markup.ID) else null
    val st = if (id != null) commands.getOrElse(id, null) else null

    if (r.kind == IsabelleProcess.Kind.STDOUT || r.kind == IsabelleProcess.Kind.STDIN)
      swing { outputInfo.fire(r.result) }
    else if (r.kind == IsabelleProcess.Kind.WRITELN && !initialized) {
      initialized = true
      swing {
        if (document != null) {
          document.activate()
          activated.fire(())
        }
      }
    }
    else {
      val tree = YXML.parse_failsafe(isabelle_symbols.decode(r.result))
      if (st == null || (st.phase != Phase.REMOVED && st.phase != Phase.REMOVE)) {
        r.kind match {

          case IsabelleProcess.Kind.STATUS =>
            //{{{ handle all kinds of status messages here
            tree match {
              case XML.Elem(Markup.MESSAGE, _, elems) =>
                for (elem <- elems) {
                  elem match {
                    //{{{
                    // command status
                    case XML.Elem(Markup.FINISHED, _, _) =>
                      st.phase = Phase.FINISHED
                      fireChange(st)
                    case XML.Elem(Markup.UNPROCESSED, _, _) =>
                      st.phase = Phase.UNPROCESSED
                      fireChange(st)
                    case XML.Elem(Markup.FAILED, _, _) =>
                      st.phase = Phase.FAILED
                      fireChange(st)
                    case XML.Elem(Markup.DISPOSED, _, _) =>
                      document.prover.commands.removeKey(st.id)
                      st.phase = Phase.REMOVED
                      fireChange(st)

                    // command and keyword declarations
                    case XML.Elem(Markup.COMMAND_DECL, List((Markup.NAME, name), (Markup.KIND, _)), _) =>
                      command_decls.addEntry(name)
                    case XML.Elem(Markup.KEYWORD_DECL, List((Markup.NAME, name)), _) =>
                      keyword_decls.addEntry(name)

                    // other markup
                    case XML.Elem(kind,
                        (Markup.OFFSET, offset) :: (Markup.END_OFFSET, end_offset) ::
                             (Markup.ID, markup_id) :: _, _) =>
                      val begin = Int.unbox(java.lang.Integer.valueOf(offset)) - 1
                      val end = Int.unbox(java.lang.Integer.valueOf(end_offset)) - 1

                      val command =
                        // outer syntax: no id in props
                        if (st == null) commands.getOrElse(markup_id, null)
                        // inner syntax: id from props
                        else st
                      command.root_node.insert(command.node_from(kind, begin, end))

                    case _ =>
                    //}}}
                  }
                }
              case _ =>
            }
            //}}}

          case IsabelleProcess.Kind.ERROR if st != null =>
            if (st.phase != Phase.REMOVED && st.phase != Phase.REMOVE)
              st.phase = Phase.FAILED
            st.add_result(tree)
            fireChange(st)

          case IsabelleProcess.Kind.WRITELN | IsabelleProcess.Kind.PRIORITY
            | IsabelleProcess.Kind.WARNING if st != null =>
            st.add_result(tree)
            fireChange(st)

          case _ =>
        }
      }
    }
  }


  def start(logic: String) {
    val results = new EventBus[IsabelleProcess.Result] + handle_result
    if (logic != null) _logic = logic
    process = new Isar(isabelle_system, results, "-m", "xsymbols", _logic)
  }

  def stop() {
    process.kill
  }

  def setDocument(text: Text, path: String) {
    this.document = new Document(text, this)
    process.ML("ThyLoad.add_path " + IsabelleSyntax.encode_string(path))

    document.structuralChanges.add(changes => {
      for (cmd <- changes.removedCommands) remove(cmd)
      for (cmd <- changes.addedCommands) send(cmd)
    })
    if (initialized) {
      document.activate()
      activated.fire(())
    }
  }

  private def send(cmd: Command) {
    cmd.phase = Phase.UNPROCESSED
    commands.put(cmd.id, cmd)

    val props = new Properties
    props.setProperty(Markup.ID, cmd.id)
    props.setProperty(Markup.OFFSET, "1")

    val content = isabelle_symbols.encode(document.getContent(cmd))
    process.create_command(props, content)
    process.insert_command(if (cmd.previous == null) "" else cmd.previous.id, cmd.id)
  }

  def remove(cmd: Command) {
    cmd.phase = Phase.REMOVE
    process.remove_command(cmd.id)
  }
}
