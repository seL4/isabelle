/*
 * Higher-level prover communication: interactive document model
 *
 * @author Johannes Hölzl, TU Munich
 * @author Fabian Immler, TU Munich
 * @author Makarius
 */

package isabelle.prover


import scala.collection.mutable
import scala.collection.immutable.{TreeSet}

import org.gjt.sp.util.Log

import isabelle.jedit.Isabelle
import isabelle.proofdocument.{ProofDocument, Text, Token}
import isabelle.IsarDocument


class Prover(isabelle_system: IsabelleSystem, logic: String)
{
  /* prover process */

  private var process: Isar = null

  {
    val results = new EventBus[IsabelleProcess.Result] + handle_result
    results.logger = Log.log(Log.ERROR, null, _)
    process = new Isar(isabelle_system, results, "-m", "xsymbols", logic)
  }

  def stop() { process.kill }

  
  /* document state information */

  private val states = new mutable.HashMap[IsarDocument.State_ID, Command]
  private val commands = new mutable.HashMap[IsarDocument.Command_ID, Command]
  private val document0 = Isabelle.plugin.id()
  private val document_versions = new mutable.HashSet[IsarDocument.Document_ID] + document0

  private var initialized = false

  
  /* outer syntax keywords */

  val decl_info = new EventBus[(String, String)]

  private val keyword_decls = new mutable.HashSet[String] {
    override def +=(name: String) = {
      decl_info.event(name, OuterKeyword.MINOR)
      super.+=(name)
    }
  }
  private val command_decls = new mutable.HashMap[String, String] {
    override def +=(entry: (String, String)) = {
      decl_info.event(entry)
      super.+=(entry)
    }
  }


  /* completions */

  var _completions = new TreeSet[String]
  def completions = _completions
  /* // TODO: ask Makarius to make Interpretation.symbols public (here: read-only as 'symbol_map')
  val map = isabelle.jedit.Isabelle.symbols.symbol_map
  for (xsymb <- map.keys) {
    _completions += xsymb
    if (map(xsymb).get("abbrev").isDefined) _completions += map(xsymb)("abbrev")
  }
  */
  decl_info += (k_v => _completions += k_v._1)


  /* event handling */

  val activated = new EventBus[Unit]
  val command_info = new EventBus[Command]
  val output_info = new EventBus[String]
  var document: ProofDocument = null


  def command_change(c: Command) = Swing.now { command_info.event(c) }

  private def handle_result(result: IsabelleProcess.Result)
  {
    val (running, command) =
      result.props.find(p => p._1 == Markup.ID) match {
        case None => (false, null)
        case Some((_, id)) =>
          if (commands.contains(id)) (false, commands(id))
          else if (states.contains(id)) (true, states(id))
          else (false, null)
      }

    if (result.kind == IsabelleProcess.Kind.STDOUT || result.kind == IsabelleProcess.Kind.STDIN)
      Swing.now { output_info.event(result.result) }
    else if (result.kind == IsabelleProcess.Kind.WRITELN && !initialized) {  // FIXME !?
      initialized = true
      Swing.now {
        if (document != null) {
          document.activate()
          activated.event(())
        }
      }
    }
    else {
      result.kind match {

        case IsabelleProcess.Kind.WRITELN | IsabelleProcess.Kind.PRIORITY
          | IsabelleProcess.Kind.WARNING | IsabelleProcess.Kind.ERROR
        if command != null =>
          if (result.kind == IsabelleProcess.Kind.ERROR)
            command.status = Command.Status.FAILED
          command.add_result(running, process.parse_message(result))
          command_change(command)

        case IsabelleProcess.Kind.STATUS =>
          //{{{ handle all kinds of status messages here
          process.parse_message(result) match {
            case XML.Elem(Markup.MESSAGE, _, elems) =>
              for (elem <- elems) {
                elem match {
                  //{{{
                  // command and keyword declarations
                  case XML.Elem(Markup.COMMAND_DECL,
                      (Markup.NAME, name) :: (Markup.KIND, kind) :: _, _) =>
                    command_decls += (name -> kind)
                  case XML.Elem(Markup.KEYWORD_DECL, (Markup.NAME, name) :: _, _) =>
                    keyword_decls += name

                  // document edits
                  case XML.Elem(Markup.EDITS, (Markup.ID, doc_id) :: _, edits)
                  if document_versions.contains(doc_id) =>
                    for {
                      XML.Elem(Markup.EDIT, (Markup.ID, cmd_id) :: (Markup.STATE, state_id) :: _, _)
                        <- edits
                      if (commands.contains(cmd_id))
                    } {
                      val cmd = commands(cmd_id)
                      if (cmd.state_id != null) states -= cmd.state_id
                      states(cmd_id) = cmd
                      cmd.state_id = state_id
                      cmd.status = Command.Status.UNPROCESSED
                      command_change(cmd)
                    }

                  // command status
                  case XML.Elem(Markup.UNPROCESSED, _, _)
                  if command != null =>
                    command.status = Command.Status.UNPROCESSED
                    command_change(command)
                  case XML.Elem(Markup.FINISHED, _, _)
                  if command != null =>
                    command.status = Command.Status.FINISHED
                    command_change(command)
                  case XML.Elem(Markup.FAILED, _, _)
                  if command != null =>
                    command.status = Command.Status.FAILED
                    command_change(command)

                  // other markup
                  case XML.Elem(kind,
                      (Markup.OFFSET, offset) :: (Markup.END_OFFSET, end_offset) ::
                           (Markup.ID, markup_id) :: _, _) =>
                    val begin = offset.toInt - 1
                    val end = end_offset.toInt - 1

                    val cmd =  // FIXME proper command version!? running!?
                      // outer syntax: no id in props
                      if (command == null) commands.getOrElse(markup_id, null)
                      // inner syntax: id from props
                      else command
                    if (cmd != null)
                      cmd.root_node.insert(cmd.node_from(kind, begin, end))

                  case _ =>
                  //}}}
                }
              }
            case _ =>
          }
          //}}}

        case _ =>
      }
    }
  }

  def set_document(text: Text, path: String) {
    this.document = new ProofDocument(text, command_decls.contains(_))
    process.ML("ThyLoad.add_path " + IsabelleSyntax.encode_string(path))

    document.structural_changes += (changes => if(initialized){
      for (cmd <- changes.removed_commands) remove(cmd)
      changes.added_commands.foldLeft (changes.before_change) ((p, c) => {send(p, c); Some(c)})
    })
  }

  private def send(prev: Option[Command], cmd: Command) {
    cmd.status = Command.Status.UNPROCESSED
    commands.put(cmd.id, cmd)

    val content = isabelle_system.symbols.encode(cmd.content)
    process.create_command(cmd.id, content)
    process.insert_command(prev match {case Some(c) => c.id case None => ""}, cmd.id)
  }

  def remove(cmd: Command) {
    commands -= cmd.id
    if (cmd.state_id != null) states -= cmd.state_id
    process.remove_command(cmd.id)
  }
}
