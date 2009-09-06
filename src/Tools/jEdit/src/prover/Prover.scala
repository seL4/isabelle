/*
 * Higher-level prover communication: interactive document model
 *
 * @author Johannes Hölzl, TU Munich
 * @author Fabian Immler, TU Munich
 * @author Makarius
 */

package isabelle.prover


import scala.collection.mutable
import scala.actors.Actor, Actor._

import javax.swing.JTextArea

import isabelle.jedit.Isabelle
import isabelle.proofdocument.{ProofDocument, Change, Token}


object ProverEvents
{
  case class Activate
}


class Prover(isabelle_system: Isabelle_System, logic: String, change_receiver: Actor)
  extends Actor
{
  /* prover process */

  private val process =
  {
    val receiver = new Actor {
      def act() {
        loop { react { case res: Isabelle_Process.Result => handle_result(res) } }
      }
    }.start
    new Isabelle_Process(isabelle_system, receiver, "-m", "xsymbols", logic)
      with Isar_Document
  }

  def stop() { process.kill }

  
  /* document state information */

  private val states = new mutable.HashMap[Isar_Document.State_ID, Command_State] with
    mutable.SynchronizedMap[Isar_Document.State_ID, Command_State]
  private val commands = new mutable.HashMap[Isar_Document.Command_ID, Command] with
    mutable.SynchronizedMap[Isar_Document.Command_ID, Command]
  val document_0 =
    ProofDocument.empty.
      set_command_keyword(command_decls.contains).
      set_change_receiver(change_receiver)
  private var document_versions = List(document_0)

  def command(id: Isar_Document.Command_ID): Option[Command] = commands.get(id)
  def document(id: Isar_Document.Document_ID) = document_versions.find(_.id == id)

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
  lazy val output_info = new EventBus[Isabelle_Process.Result]

  val output_text_view = new JTextArea
  output_info += (result => output_text_view.append(result.toString + "\n"))

  private def handle_result(result: Isabelle_Process.Result)
  {
    val state =
      result.props.find(p => p._1 == Markup.ID) match {
        case None => None
        case Some((_, id)) =>
          if (commands.contains(id)) Some(commands(id))
          else if (states.contains(id)) Some(states(id))
          else None
      }
    output_info.event(result)
    val message = Isabelle_Process.parse_message(isabelle_system, result)

    if (state.isDefined) state.get ! message
    else result.kind match {

      case Isabelle_Process.Kind.STATUS =>
        //{{{ handle all kinds of status messages here
        message match {
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
                  val doc = document_versions.find(_.id == doc_id).get
                  for {
                    XML.Elem(Markup.EDIT, (Markup.ID, cmd_id) :: (Markup.STATE, state_id) :: _, _)
                      <- edits
                  } {
                    if (commands.contains(cmd_id)) {
                      val cmd = commands(cmd_id)
                      val state = new Command_State(cmd)
                      states(state_id) = state
                      doc.states += (cmd -> state)
                      cmd.changed()
                    }

                  }
                case XML.Elem(kind, attr, body) =>
                  // TODO: This is mostly irrelevant information on removed commands, but it can
                  // also be outer-syntax-markup since there is no id in props (fix that?)
                  val (begin, end) = Position.offsets_of(attr)
                  val markup_id = Position.id_of(attr)
                  val outer = isabelle.jedit.DynamicTokenMarker.is_outer(kind)
                  if (outer && begin.isDefined && end.isDefined && markup_id.isDefined)
                    commands.get(markup_id.get).map (cmd => cmd ! message)
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

  def act() {
    loop {
      react {
        case change: Change =>
          val old = document(change.parent.get.id).get
          val (doc, structure_change) = old.text_changed(change)
          document_versions ::= doc
          edit_document(old, doc, structure_change)
          change_receiver ! doc
        case x => System.err.println("warning: ignored " + x)
      }
    }
  }

  def set_document(path: String) {
    process.begin_document(document_0.id, path)
  }

  private def edit_document(old: ProofDocument, doc: ProofDocument,
    changes: ProofDocument.StructureChange) =
  {
    val id_changes = changes map { case (c1, c2) =>
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
