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

import scala.actors.Actor
import scala.actors.Actor._

import org.gjt.sp.util.Log
import javax.swing.JTextArea

import isabelle.jedit.Isabelle
import isabelle.proofdocument.{ProofDocument, Change, Token}
import isabelle.IsarDocument

object ProverEvents {
  case class Activate
}

class Prover(isabelle_system: Isabelle_System, logic: String) extends Actor
{
  /* prover process */

  private val process =
  {
    val results = new EventBus[Isabelle_Process.Result] + handle_result
    results.logger = Log.log(Log.ERROR, null, _)
    new Isabelle_Process(isabelle_system, results, "-m", "xsymbols", logic) with IsarDocument
  }

  def stop() { process.kill }

  
  /* document state information */

  private val states = new mutable.HashMap[IsarDocument.State_ID, Command] with
    mutable.SynchronizedMap[IsarDocument.State_ID, Command]
  private val commands = new mutable.HashMap[IsarDocument.Command_ID, Command] with
    mutable.SynchronizedMap[IsarDocument.Command_ID, Command]
  val document_0 =
    ProofDocument.empty.set_command_keyword(command_decls.contains)
  private var document_versions = List(document_0)

  def command(id: IsarDocument.Command_ID): Option[Command] = commands.get(id)
  def document(id: IsarDocument.Document_ID) = document_versions.find(_.id == id)

  private var initialized = false

  
  /* outer syntax keywords */

  val decl_info = new EventBus[(String, String)]

  private val keyword_decls =
    new mutable.HashSet[String] with mutable.SynchronizedSet[String] {
    override def +=(name: String) = {
      decl_info.event(name, OuterKeyword.MINOR)
      super.+=(name)
    }
  }
  private val command_decls =
    new mutable.HashMap[String, String] with mutable.SynchronizedMap[String, String] {
    override def +=(entry: (String, String)) = {
      decl_info.event(entry)
      super.+=(entry)
    }
  }


  /* completions */

  private var _completion = Isabelle.completion
  def completion = _completion
  decl_info += (p => _completion += p._1)


  /* event handling */
  val output_info = new EventBus[Isabelle_Process.Result]
  var change_receiver: Actor = null

  val output_text_view = new JTextArea
  output_info += (result => output_text_view.append(result.toString + "\n"))

  private def handle_result(result: Isabelle_Process.Result)
  {
    def command_change(c: Command) = change_receiver ! c
    val (state, command) =
      result.props.find(p => p._1 == Markup.ID) match {
        case None => (null, null)
        case Some((_, id)) =>
          if (commands.contains(id)) (null, commands(id))
          else if (states.contains(id)) (id, states(id))
          else (null, null)
      }

    if (result.kind == Isabelle_Process.Kind.STDOUT ||
        result.kind == Isabelle_Process.Kind.STDIN)
      output_info.event(result)
    else {
      result.kind match {

        case Isabelle_Process.Kind.WRITELN
        | Isabelle_Process.Kind.PRIORITY
        | Isabelle_Process.Kind.WARNING
        | Isabelle_Process.Kind.ERROR =>
          if (command != null) {
            if (result.kind == Isabelle_Process.Kind.ERROR)
              command.set_status(state, Command.Status.FAILED)
            command.add_result(state, process.parse_message(result))
            command_change(command)
          } else {
            output_info.event(result)
          }

        case Isabelle_Process.Kind.STATUS =>
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

                  // process ready (after initialization)
                  case XML.Elem(Markup.READY, _, _)
                  if !initialized =>
                    initialized = true
                    change_receiver ! ProverEvents.Activate

                  // document edits
                  case XML.Elem(Markup.EDITS, (Markup.ID, doc_id) :: _, edits)
                  if document_versions.exists(_.id == doc_id) =>
                    output_info.event(result)
                    val doc = document_versions.find(_.id == doc_id).get
                    for {
                      XML.Elem(Markup.EDIT, (Markup.ID, cmd_id) :: (Markup.STATE, state_id) :: _, _)
                        <- edits
                    } {
                      if (commands.contains(cmd_id)) {
                        val cmd = commands(cmd_id)
                        states(state_id) = cmd
                        doc.states += (cmd -> state_id)
                        cmd.states += (state_id -> new Command_State(cmd))
                        command_change(cmd)
                      }

                    }
                  // command status
                  case XML.Elem(Markup.UNPROCESSED, _, _)
                  if command != null =>
                    output_info.event(result)
                    command.set_status(state, Command.Status.UNPROCESSED)
                    command_change(command)
                  case XML.Elem(Markup.FINISHED, _, _)
                  if command != null =>
                    output_info.event(result)
                    command.set_status(state, Command.Status.FINISHED)
                    command_change(command)
                  case XML.Elem(Markup.FAILED, _, _)
                  if command != null =>
                    output_info.event(result)
                    command.set_status(state, Command.Status.FAILED)
                    command_change(command)
                  case XML.Elem(kind, attr, body)
                  if command != null =>
                    val (begin, end) = Position.offsets_of(attr)
                    if (begin.isDefined && end.isDefined) {
                      if (kind == Markup.ML_TYPING) {
                        val info = body.first.asInstanceOf[XML.Text].content
                        command.add_markup(state,
                          command.markup_node(begin.get - 1, end.get - 1, TypeInfo(info)))
                      } else if (kind == Markup.ML_REF) {
                        body match {
                          case List(XML.Elem(Markup.ML_DEF, attr, _)) =>
                            command.add_markup(state, command.markup_node(
                              begin.get - 1, end.get - 1,
                              RefInfo(
                                Position.file_of(attr),
                                Position.line_of(attr),
                                Position.id_of(attr),
                                Position.offset_of(attr))))
                          case _ =>
                        }
                      } else {
                        command.add_markup(state,
                          command.markup_node(begin.get - 1, end.get - 1, HighlightInfo(kind)))
                      }
                    }
                    command_change(command)
                  case XML.Elem(kind, attr, body)
                  if command == null =>
                    // TODO: This is mostly irrelevant information on removed commands, but it can
                    // also be outer-syntax-markup since there is no id in props (fix that?)
                    val (begin, end) = Position.offsets_of(attr)
                    val markup_id = Position.id_of(attr)
                    val outer = isabelle.jedit.DynamicTokenMarker.is_outer(kind)
                    if (outer && state == null && begin.isDefined && end.isDefined && markup_id.isDefined)
                      commands.get(markup_id.get).map (cmd => {
                        cmd.add_markup(state,
                          cmd.markup_node(begin.get - 1, end.get - 1, OuterInfo(kind)))
                        command_change(cmd)
                      })
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

  def act() {
    import ProverEvents._
    loop {
      react {
        case change: Change => {
            val old = document(change.parent.get.id).get
            val (doc, structure_change) = old.text_changed(change)
            document_versions ::= doc
            edit_document(old, doc, structure_change)
        }
        case x => System.err.println("warning: ignored " + x)
      }
    }
  }
  
  def set_document(change_receiver: Actor, path: String) {
    this.change_receiver = change_receiver
    process.begin_document(document_0.id, path)
  }

  private def edit_document(old: ProofDocument, doc: ProofDocument,
                            changes: ProofDocument.StructureChange) = {
    val id_changes = changes map {case (c1, c2) =>
      (c1.map(_.id).getOrElse(document_0.id),
      c2 match {
        case None => None
        case Some(cmd) =>
          commands += (cmd.id -> cmd)
          process.define_command(cmd.id, isabelle_system.symbols.encode(cmd.content))
          Some(cmd.id)
      })
    }
    process.edit_document(old.id, doc.id, id_changes)
  }
}
