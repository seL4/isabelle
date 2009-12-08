/*
 * Higher-level prover communication: interactive document model
 *
 * @author Johannes Hölzl, TU Munich
 * @author Fabian Immler, TU Munich
 * @author Makarius
 */

package isabelle.proofdocument


import scala.actors.Actor, Actor._

import javax.swing.JTextArea

import isabelle.jedit.Isabelle


class Prover(system: Isabelle_System, logic: String)
{
  /* incoming messages */

  private var prover_ready = false

  private val receiver = new Actor {
    def act() {
      loop {
        react {
          case result: Isabelle_Process.Result => handle_result(result)
          case change: Change if prover_ready => handle_change(change)
          case bad if prover_ready => System.err.println("prover: ignoring bad message " + bad)
        }
      }
    }
  }

  def input(change: Change) { receiver ! change }


  /* outgoing messages */

  val command_change = new Event_Bus[Command]
  val document_change = new Event_Bus[Proof_Document]


  /* prover process */

  private val process =
    new Isabelle_Process(system, receiver, "-m", "xsymbols", logic) with Isar_Document


  /* outer syntax keywords and completion */

  @volatile private var _command_decls = Map[String, String]()
  def command_decls() = _command_decls

  @volatile private var _keyword_decls = Set[String]()
  def keyword_decls() = _keyword_decls

  @volatile private var _completion = Isabelle.completion
  def completion() = _completion


  /* document state information */

  @volatile private var states = Map[Isar_Document.State_ID, Command_State]()
  @volatile private var commands = Map[Isar_Document.Command_ID, Command]()
  val document_0 =
    Proof_Document.empty.
    set_command_keyword((s: String) => command_decls().contains(s))
  @volatile private var document_versions = List(document_0)

  def command(id: Isar_Document.Command_ID): Option[Command] = commands.get(id)
  def document(id: Isar_Document.Document_ID): Option[Proof_Document] =
    document_versions.find(_.id == id)


  /* prover results */

  val output_text_view = new JTextArea    // FIXME separate jEdit component

  private def handle_result(result: Isabelle_Process.Result)
  {
    // FIXME separate jEdit component
    Swing_Thread.later { output_text_view.append(result.toString + "\n") }

    val message = Isabelle_Process.parse_message(system, result)

    val state =
      Position.id_of(result.props) match {
        case None => None
        case Some(id) => commands.get(id) orElse states.get(id) orElse None
      }
    if (state.isDefined) state.get ! (this, message)
    else if (result.kind == Isabelle_Process.Kind.STATUS) {
      //{{{ global status message
      message match {
        case XML.Elem(Markup.MESSAGE, _, elems) =>
          for (elem <- elems) {
            elem match {
              // document edits
              case XML.Elem(Markup.EDITS, (Markup.ID, doc_id) :: _, edits) =>
                document_versions.find(_.id == doc_id) match {
                  case Some(doc) =>
                    for {
                      XML.Elem(Markup.EDIT, (Markup.ID, cmd_id) :: (Markup.STATE, state_id) :: _, _)
                      <- edits }
                    {
                      commands.get(cmd_id) match {
                        case Some(cmd) =>
                          val state = new Command_State(cmd)
                          states += (state_id -> state)
                          doc.states += (cmd -> state)
                          command_change.event(cmd)   // FIXME really!?
                        case None =>
                      }
                    }
                  case None =>
                }

              // command and keyword declarations
              case XML.Elem(Markup.COMMAND_DECL, (Markup.NAME, name) :: (Markup.KIND, kind) :: _, _) =>
                _command_decls += (name -> kind)
                _completion += name
              case XML.Elem(Markup.KEYWORD_DECL, (Markup.NAME, name) :: _, _) =>
                _keyword_decls += name
                _completion += name

              // process ready (after initialization)
              case XML.Elem(Markup.READY, _, _) => prover_ready = true

              case _ =>
            }
          }
        case _ =>
      }
      //}}}
    }
  }


  /* document changes */

  def begin_document(path: String) {
    process.begin_document(document_0.id, path)
  }

  def handle_change(change: Change) {
    val old = document(change.parent.get.id).get
    val (doc, changes) = old.text_changed(change)
    document_versions ::= doc

    val id_changes = changes map { case (c1, c2) =>
        (c1.map(_.id).getOrElse(document_0.id),
         c2 match {
            case None => None
            case Some(command) =>
              commands += (command.id -> command)
              process.define_command(command.id, system.symbols.encode(command.content))
              Some(command.id)
          })
    }
    process.edit_document(old.id, doc.id, id_changes)

    document_change.event(doc)
  }


  /* main controls */

  def start() { receiver.start() }

  def stop() { process.kill() }
}
