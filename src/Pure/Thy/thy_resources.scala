/*  Title:      Pure/Thy/thy_resources.scala
    Author:     Makarius

PIDE resources for theory files: load/unload theories via PIDE document updates.
*/

package isabelle


import java.io.{File => JFile}


object Thy_Resources
{
  /* PIDE session */

  def start_session(
    options: Options,
    session_name: String,
    session_dirs: List[Path] = Nil,
    include_sessions: List[String] = Nil,
    session_base: Option[Sessions.Base] = None,
    print_mode: List[String] = Nil,
    progress: Progress = No_Progress,
    log: Logger = No_Logger): Session =
  {
    val base =
      session_base getOrElse
        Sessions.base_info(options, session_name, include_sessions = include_sessions,
          progress = progress, dirs = session_dirs).check_base
    val resources = new Thy_Resources(base, log = log)
    val session = new Session(session_name, options, resources)

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

    def messages(node_name: Document.Node.Name): List[(XML.Tree, Position.T)] =
    {
      val node = version.nodes(node_name)
      (for {
        (command, start) <-
          Document.Node.Commands.starts_pos(node.commands.iterator, Token.Pos.file(node_name.node))
        pos = command.span.keyword_pos(start).position(command.span.name)
        (_, tree) <- state.command_results(version, command).iterator
       } yield (tree, pos)).toList
    }
  }

  class Session private[Thy_Resources](
    session_name: String,
    session_options: Options,
    override val resources: Thy_Resources) extends isabelle.Session(session_options, resources)
  {
    session =>

    val tmp_dir: JFile = Isabelle_System.tmp_dir("server_session")
    val tmp_dir_name: String = File.path(tmp_dir).implode

    override def toString: String = session_name

    override def stop(): Process_Result =
    {
      try { super.stop() }
      finally { Isabelle_System.rm_tree(tmp_dir) }
    }


    /* theories */

    def use_theories(
      theories: List[String],
      qualifier: String = Sessions.DRAFT,
      master_dir: String = "",
      id: UUID = UUID(),
      progress: Progress = No_Progress): Theories_Result =
    {
      val dep_theories =
        resources.load_theories(session, id, theories, qualifier = qualifier,
          master_dir = proper_string(master_dir) getOrElse tmp_dir_name, progress = progress)

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

      val check_progress =
        Event_Timer.request(Time.now(), repeat = Some(Time.seconds(0.5)))
          { if (progress.stopped) result.cancel else check_state }

      val consumer =
        Session.Consumer[Session.Commands_Changed](getClass.getName) {
          case changed => if (dep_theories.exists(changed.nodes)) check_state
        }

      try {
        session.commands_changed += consumer
        result.join_result
        check_progress.cancel
        session.commands_changed -= consumer
      }
      finally {
        resources.unload_theories(session, id, dep_theories)
      }

      result.join
    }

    def purge_theories(
        theories: List[String],
        qualifier: String = Sessions.DRAFT,
        master_dir: String = "",
        all: Boolean = false): (List[Document.Node.Name], List[Document.Node.Name]) =
      resources.purge_theories(session, theories = theories, qualifier = qualifier,
        master_dir = proper_string(master_dir) getOrElse tmp_dir_name, all = all)
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

    def remove_theories(remove: List[Document.Node.Name]): State =
    {
      require(remove.forall(name => !is_required(name)))
      copy(theories = theories -- remove)
    }

    lazy val theories_graph: Graph[Document.Node.Name, Unit] =
    {
      val entries =
        for ((name, theory) <- theories.toList)
        yield ((name, ()), theory.node_header.imports.map(_._1).filter(theories.isDefinedAt(_)))
      Graph.make(entries, symmetric = true)(Document.Node.Name.Ordering)
    }
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

    def make_edits(text_edits: List[Text.Edit]): List[Document.Edit_Text] =
      List(node_name -> Document.Node.Deps(node_header),
        node_name -> Document.Node.Edits(text_edits),
        node_name -> node_perspective)

    def node_edits(old: Option[Theory]): List[Document.Edit_Text] =
    {
      val (text_edits, old_required) =
        if (old.isEmpty) (Text.Edit.inserts(0, text), false)
        else (Text.Edit.replace(0, old.get.text, text), old.get.node_required)

      if (text_edits.isEmpty && node_required == old_required) Nil
      else make_edits(text_edits)
    }

    def purge_edits: List[Document.Edit_Text] =
      make_edits(Text.Edit.removes(0, text))

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
    theories: List[String],
    qualifier: String,
    master_dir: String,
    progress: Progress): List[Document.Node.Name] =
  {
    val import_names = theories.map(thy => import_name(qualifier, master_dir, thy) -> Position.none)
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

    state.change(st =>
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
        session.update(Document.Blobs.empty, theory_edits.flatMap(_._1))
        st1.update_theories(theory_edits.map(_._2))
      })

    dep_theories
  }

  def unload_theories(session: Session, id: UUID, dep_theories: List[Document.Node.Name])
  {
    state.change(st =>
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
        session.update(Document.Blobs.empty, theory_edits.flatMap(_._1))
        st1.update_theories(theory_edits.map(_._2))
      })
  }

  def purge_theories(session: Session,
    theories: List[String],
    qualifier: String,
    master_dir: String,
    all: Boolean): (List[Document.Node.Name], List[Document.Node.Name]) =
  {
    val nodes = theories.map(import_name(qualifier, master_dir, _))

    state.change_result(st =>
      {
        val graph = st.theories_graph
        val all_nodes = graph.topological_order

        val purge =
          (if (all) all_nodes else nodes.filter(graph.defined(_))).
            filterNot(st.is_required(_)).toSet

        val retain = graph.all_preds(all_nodes.filterNot(purge)).toSet
        val (retained, purged) = all_nodes.partition(retain)

        val purge_edits = purged.flatMap(name => st.theories(name).purge_edits)
        session.update(Document.Blobs.empty, purge_edits)

        ((purged, retained), st.remove_theories(purged))
      })
  }
}
