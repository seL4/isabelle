/*
 * Higher-level prover communication
 *
 * @author Johannes Hölzl, TU Munich
 * @author Fabian Immler, TU Munich
 * @author Makarius
 */

package isabelle.prover


import java.util.Properties

import scala.collection.mutable.{HashMap, HashSet}

import org.gjt.sp.util.Log

import isabelle.proofdocument.{ProofDocument, Text, Token}


class Prover(isabelle_system: IsabelleSystem, isabelle_symbols: Symbol.Interpretation)
{
  private var _logic = isabelle_system.getenv_strict("ISABELLE_LOGIC")
  private var process: Isar = null
  private var commands = new HashMap[String, Command]

  val decl_info = new EventBus[(String, String)]
  val command_decls = new HashSet[String]{
    override def +=(elem : String) = {
      decl_info.event(elem, Markup.COMMAND)
      this += elem
    }
  }
  val keyword_decls = new HashSet[String]{
    override def +=(elem : String) = {
      decl_info.event(elem, Markup.KEYWORD)
      this += elem
    }
  }
  private var initialized = false

  val activated = new EventBus[Unit]
  val command_info = new EventBus[Command]
  val output_info = new EventBus[String]
  var document: Document = null


  def command_change(c: Command) = Swing.now { command_info.event(c) }

  private def handle_result(r: IsabelleProcess.Result) = {
    val id = if (r.props != null) r.props.getProperty(Markup.ID) else null
    val st = if (id != null) commands.getOrElse(id, null) else null

    if (r.kind == IsabelleProcess.Kind.STDOUT || r.kind == IsabelleProcess.Kind.STDIN)
      Swing.now { output_info.event(r.result) }
    else if (r.kind == IsabelleProcess.Kind.WRITELN && !initialized) {
      initialized = true
      Swing.now {
        if (document != null) {
          document.activate()
          activated.event(())
        }
      }
    }
    else {
      val tree = YXML.parse_failsafe(isabelle_symbols.decode(r.result))
      if (st == null || (st.status != Command.Status.REMOVED && st.status != Command.Status.REMOVE)) {
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
                      st.status = Command.Status.FINISHED
                      command_change(st)
                    case XML.Elem(Markup.UNPROCESSED, _, _) =>
                      st.status = Command.Status.UNPROCESSED
                      command_change(st)
                    case XML.Elem(Markup.FAILED, _, _) =>
                      st.status = Command.Status.FAILED
                      command_change(st)
                    case XML.Elem(Markup.DISPOSED, _, _) =>
                      document.prover.commands.removeKey(st.id)
                      st.status = Command.Status.REMOVED
                      command_change(st)

                    // command and keyword declarations
                    case XML.Elem(Markup.COMMAND_DECL, (Markup.NAME, name) :: _, _) =>
                      command_decls += name
                    case XML.Elem(Markup.KEYWORD_DECL, (Markup.NAME, name) :: _, _) =>
                      keyword_decls += name

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
            if (st.status != Command.Status.REMOVED && st.status != Command.Status.REMOVE)
              st.status = Command.Status.FAILED
            st.add_result(tree)
            command_change(st)

          case IsabelleProcess.Kind.WRITELN | IsabelleProcess.Kind.PRIORITY
            | IsabelleProcess.Kind.WARNING if st != null =>
            st.add_result(tree)
            command_change(st)

          case _ =>
        }
      }
    }
  }


  def start(logic: String) {
    if (logic != null) _logic = logic

    val results = new EventBus[IsabelleProcess.Result]
    results += handle_result
    results.logger = Log.log(Log.ERROR, null, _)

    process = new Isar(isabelle_system, results, "-m", "xsymbols", _logic)
  }

  def stop() {
    process.kill
  }

  def set_document(text: Text, path: String) {
    this.document = new Document(text, this)
    process.ML("ThyLoad.add_path " + IsabelleSyntax.encode_string(path))

    document.structural_changes += (changes => {
      for (cmd <- changes.removedCommands) remove(cmd)
      for (cmd <- changes.addedCommands) send(cmd)
    })
    if (initialized) {
      document.activate()
      activated.event(())
    }
  }

  private def send(cmd: Command) {
    cmd.status = Command.Status.UNPROCESSED
    commands.put(cmd.id, cmd)

    val content = isabelle_symbols.encode(document.getContent(cmd))
    process.create_command(cmd.id, content)
    process.insert_command(if (cmd.previous == null) "" else cmd.previous.id, cmd.id)
  }

  def remove(cmd: Command) {
    cmd.status = Command.Status.REMOVE
    process.remove_command(cmd.id)
  }
}
