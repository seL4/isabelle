/*  Title:      Pure/Thy/thy_resources.scala
    Author:     Makarius

PIDE resources for theory files.
*/

package isabelle


object Thy_Resources
{
  /* PIDE session */

  def start_session(
    options: Options,
    session_name: String,
    session_dirs: List[Path] = Nil,
    session_base: Option[Sessions.Base] = None,
    print_mode: List[String] = Nil,
    progress: Progress = No_Progress,
    log: Logger = No_Logger): Session =
  {
    val base =
      session_base getOrElse
      Sessions.base_info(options, session_name, progress = progress, dirs = session_dirs).check_base
    val resources = new Thy_Resources(base, log = log)
    val session = new Session(options, resources)

    val session_error = Future.promise[String]
    var session_phase: Session.Consumer[Session.Phase] = null
    session_phase =
      Session.Consumer(getClass.getName) {
        case Session.Ready =>
          session.phase_changed -= session_phase
          session_error.fulfill("")
        case Session.Terminated(result) if !result.ok =>
          session.phase_changed -= session_phase
          session_error.fulfill("Session start failed: return code " + result.rc)
        case _ =>
      }
    session.phase_changed += session_phase

    progress.echo("Starting " + session_name + " ...")
    Isabelle_Process.start(session, options,
      logic = session_name, dirs = session_dirs, modes = print_mode)

    session_error.join match {
      case "" => session
      case msg => session.stop(); error(msg)
    }
  }

  sealed case class Theories_Result(
    val state: Document.State,
    val version: Document.Version,
    val nodes: List[(Document.Node.Name, Protocol.Node_Status)])
  {
    def ok: Boolean = nodes.forall({ case (_, st) => st.ok })
  }

  class Session private[Thy_Resources](
    session_options: Options,
    override val resources: Thy_Resources) extends isabelle.Session(session_options, resources)
  {
    session =>

    def use_theories(
      theories: List[(String, Position.T)],
      qualifier: String = Sessions.DRAFT,
      master_dir: String = "",
      id: UUID = UUID(),
      progress: Progress = No_Progress): Theories_Result =
    {
      val dep_theories =
        resources.load_theories(session, id, theories, qualifier = qualifier,
          master_dir = master_dir, progress = progress)

      val result = Future.promise[Theories_Result]

      def check_state
      {
        val state = session.current_state()
        state.stable_tip_version match {
          case Some(version) if dep_theories.forall(state.node_consolidated(version, _)) =>
            val nodes =
              for (name <- dep_theories)
              yield (name -> Protocol.node_status(state, version, name, version.nodes(name)))
            try { result.fulfill(Theories_Result(state, version, nodes)) }
            catch { case _: IllegalStateException => }
          case _ =>
        }
      }

      val consumer =
        Session.Consumer[Session.Commands_Changed](getClass.getName) {
          case changed => if (dep_theories.exists(changed.nodes)) check_state
        }

      session.commands_changed += consumer
      check_state
      result.join
      session.commands_changed -= consumer

      resources.unload_theories(session, id, dep_theories)

      result.join
    }
  }


  /* internal state */

  sealed case class State(
    required: Multi_Map[Document.Node.Name, UUID] = Multi_Map.empty,
    theories: Map[Document.Node.Name, Theory] = Map.empty)
  {
    def is_required(name: Document.Node.Name): Boolean = required.isDefinedAt(name)

    def insert_required(id: UUID, names: List[Document.Node.Name]): State =
      copy(required = (required /: names)(_.insert(_, id)))

    def remove_required(id: UUID, names: List[Document.Node.Name]): State =
      copy(required = (required /: names)(_.remove(_, id)))

    def update_theories(update: List[(Document.Node.Name, Theory)]): State =
      copy(theories =
        (theories /: update)({ case (thys, (name, thy)) =>
          thys.get(name) match {
            case Some(thy1) if thy1 == thy => thys
            case _ => thys + (name -> thy)
          }
        }))
  }

  final class Theory private[Thy_Resources](
    val node_name: Document.Node.Name,
    val node_header: Document.Node.Header,
    val text: String,
    val node_required: Boolean)
  {
    override def toString: String = node_name.toString

    def node_perspective: Document.Node.Perspective_Text =
      Document.Node.Perspective(node_required, Text.Perspective.empty, Document.Node.Overlays.empty)

    def node_edits(old: Option[Theory]): List[Document.Edit_Text] =
    {
      val (text_edits, old_required) =
        if (old.isEmpty) (Text.Edit.inserts(0, text), false)
        else (Text.Edit.replace(0, old.get.text, text), old.get.node_required)

      if (text_edits.isEmpty && node_required == old_required) Nil
      else
        List(node_name -> Document.Node.Deps(node_header),
          node_name -> Document.Node.Edits(text_edits),
          node_name -> node_perspective)
    }

    def required(required: Boolean): Theory =
      if (required == node_required) this
      else new Theory(node_name, node_header, text, required)
  }
}

class Thy_Resources(session_base: Sessions.Base, log: Logger = No_Logger)
  extends Resources(session_base, log = log)
{
  resources =>

  private val state = Synchronized(Thy_Resources.State())

  def load_theories(
    session: Session,
    id: UUID,
    theories: List[(String, Position.T)],
    qualifier: String = Sessions.DRAFT,
    master_dir: String = "",
    progress: Progress = No_Progress): List[Document.Node.Name] =
  {
    val import_names =
      for ((thy, pos) <- theories)
      yield (import_name(qualifier, master_dir, thy), pos)

    val dependencies = resources.dependencies(import_names, progress = progress).check_errors
    val dep_theories = dependencies.theories

    val loaded_theories =
      for (node_name <- dep_theories)
      yield {
        val path = node_name.path
        if (!node_name.is_theory) error("Not a theory file: " + path)

        progress.expose_interrupt()
        val text = File.read(path)
        val node_header = resources.check_thy_reader(node_name, Scan.char_reader(text))
        new Thy_Resources.Theory(node_name, node_header, text, true)
      }

    val edits =
      state.change_result(st =>
        {
          val st1 = st.insert_required(id, dep_theories)
          val theory_edits =
            for (theory <- loaded_theories)
            yield {
              val node_name = theory.node_name
              val theory1 = theory.required(st1.is_required(node_name))
              val edits = theory1.node_edits(st1.theories.get(node_name))
              (edits, (node_name, theory1))
            }
          (theory_edits.flatMap(_._1), st1.update_theories(theory_edits.map(_._2)))
        })
    session.update(Document.Blobs.empty, edits)

    dep_theories
  }

  def unload_theories(session: Session, id: UUID, dep_theories: List[Document.Node.Name])
  {
    val edits =
      state.change_result(st =>
        {
          val st1 = st.remove_required(id, dep_theories)
          val theory_edits =
            for {
              node_name <- dep_theories
              theory <- st1.theories.get(node_name)
            }
            yield {
              val theory1 = theory.required(st1.is_required(node_name))
              val edits = theory1.node_edits(Some(theory))
              (edits, (node_name, theory1))
            }
          (theory_edits.flatMap(_._1), st1.update_theories(theory_edits.map(_._2)))
        })
    session.update(Document.Blobs.empty, edits)
  }
}
