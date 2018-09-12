/*  Title:      Pure/Thy/thy_resources.scala
    Author:     Makarius

PIDE resources for theory files: load/unload theories via PIDE document updates.
*/

package isabelle


import java.io.{File => JFile}

import scala.annotation.tailrec


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

  private def stable_snapshot(
    state: Document.State, version: Document.Version, name: Document.Node.Name): Document.Snapshot =
  {
    val snapshot = state.snapshot(name)
    assert(version.id == snapshot.version.id)
    snapshot
  }

  class Theories_Result private[Thy_Resources](
    val state: Document.State,
    val version: Document.Version,
    val nodes: List[(Document.Node.Name, Document_Status.Node_Status)],
    val nodes_committed: List[(Document.Node.Name, Document_Status.Node_Status)])
  {
    def snapshot(name: Document.Node.Name): Document.Snapshot =
      stable_snapshot(state, version, name)

    def ok: Boolean =
      (nodes.iterator ++ nodes_committed.iterator).forall({ case (_, st) => st.ok })
  }

  val default_check_delay = Time.seconds(0.5)
  val default_nodes_status_delay = Time.seconds(-1.0)
  val default_commit_cleanup_delay = Time.seconds(60.0)
  val default_watchdog_timeout = Time.seconds(600.0)


  class Session private[Thy_Resources](
    session_name: String,
    session_options: Options,
    override val resources: Thy_Resources) extends isabelle.Session(session_options, resources)
  {
    session =>


    /* temporary directory */

    val tmp_dir: JFile = Isabelle_System.tmp_dir("server_session")
    val tmp_dir_name: String = File.path(tmp_dir).implode

    def master_directory(master_dir: String): String =
      proper_string(master_dir) getOrElse tmp_dir_name

    override def toString: String = session_name

    override def stop(): Process_Result =
    {
      try { super.stop() }
      finally { Isabelle_System.rm_tree(tmp_dir) }
    }


    /* theories */

    private sealed case class Use_Theories_State(
      last_update: Time = Time.now(),
      nodes_status: Document_Status.Nodes_Status = Document_Status.Nodes_Status.empty,
      already_committed: Map[Document.Node.Name, Document_Status.Node_Status] = Map.empty,
      result: Promise[Theories_Result] = Future.promise[Theories_Result])
    {
      def update(new_nodes_status: Document_Status.Nodes_Status): Use_Theories_State =
        copy(last_update = Time.now(), nodes_status = new_nodes_status)

      def watchdog(watchdog_timeout: Time): Boolean =
        watchdog_timeout > Time.zero && Time.now() - last_update > watchdog_timeout

      def cancel_result { result.cancel }
      def finished_result: Boolean = result.is_finished
      def await_result { result.join_result }
      def join_result: Theories_Result = result.join
      def check_result(
          state: Document.State,
          version: Document.Version,
          dep_theories: List[Document.Node.Name],
          beyond_limit: Boolean,
          watchdog_timeout: Time,
          commit: Option[(Document.Snapshot, Document_Status.Node_Status) => Unit])
        : Use_Theories_State =
      {
        val st1 =
          if (commit.isDefined) {
            val already_committed1 =
              (already_committed /: dep_theories)({ case (committed, name) =>
                def parents_committed: Boolean =
                  version.nodes(name).header.imports.forall({ case (parent, _) =>
                    Sessions.is_pure(parent.theory) || committed.isDefinedAt(parent)
                  })
                if (!committed.isDefinedAt(name) && parents_committed &&
                    state.node_consolidated(version, name))
                {
                  val snapshot = stable_snapshot(state, version, name)
                  val status = Document_Status.Node_Status.make(state, version, name)
                  commit.get.apply(snapshot, status)
                  committed + (name -> status)
                }
                else committed
              })
            copy(already_committed = already_committed1)
          }
          else this

        if (beyond_limit || watchdog(watchdog_timeout) ||
          dep_theories.forall(name =>
            already_committed.isDefinedAt(name) ||
            state.node_consolidated(version, name) ||
            nodes_status.quasi_consolidated(name)))
        {
          val nodes =
            for (name <- dep_theories)
            yield { (name -> Document_Status.Node_Status.make(state, version, name)) }
          val nodes_committed =
            for {
              name <- dep_theories
              status <- already_committed.get(name)
            } yield (name -> status)

          try { result.fulfill(new Theories_Result(state, version, nodes, nodes_committed)) }
          catch { case _: IllegalStateException => }
        }

        st1
      }
    }

    def use_theories(
      theories: List[String],
      qualifier: String = Sessions.DRAFT,
      master_dir: String = "",
      check_delay: Time = default_check_delay,
      check_limit: Int = 0,
      watchdog_timeout: Time = default_watchdog_timeout,
      nodes_status_delay: Time = default_nodes_status_delay,
      id: UUID = UUID(),
      // commit: must not block, must not fail
      commit: Option[(Document.Snapshot, Document_Status.Node_Status) => Unit] = None,
      commit_cleanup_delay: Time = default_commit_cleanup_delay,
      progress: Progress = No_Progress): Theories_Result =
    {
      val dep_theories =
      {
        val import_names =
          theories.map(thy =>
            resources.import_name(qualifier, master_directory(master_dir), thy) -> Position.none)
        resources.dependencies(import_names, progress = progress).check_errors.theories
      }

      val use_theories_state = Synchronized(Use_Theories_State())

      def check_result(beyond_limit: Boolean = false)
      {
        val state = session.current_state()
        state.stable_tip_version match {
          case Some(version) =>
            use_theories_state.change(
              _.check_result(state, version, dep_theories, beyond_limit, watchdog_timeout, commit))
          case None =>
        }
      }

      val check_progress =
      {
        var check_count = 0
        Event_Timer.request(Time.now(), repeat = Some(check_delay))
          {
            if (progress.stopped) use_theories_state.value.cancel_result
            else {
              check_count += 1
              check_result(check_limit > 0 && check_count > check_limit)
            }
          }
      }

      val consumer =
      {
        val delay_nodes_status =
          Standard_Thread.delay_first(nodes_status_delay max Time.zero) {
            progress.nodes_status(use_theories_state.value.nodes_status)
          }

        val delay_commit_clean =
          Standard_Thread.delay_first(commit_cleanup_delay max Time.zero) {
            val clean = use_theories_state.value.already_committed.keySet
            resources.clean_theories(session, id, clean)
          }

        val dep_theories_set = dep_theories.toSet

        Session.Consumer[Session.Commands_Changed](getClass.getName) {
          case changed =>
            if (changed.nodes.exists(dep_theories_set)) {
              val snapshot = session.snapshot()
              val state = snapshot.state
              val version = snapshot.version

              val theory_progress =
                use_theories_state.change_result(st =>
                  {
                    val domain =
                      if (st.nodes_status.is_empty) dep_theories_set
                      else changed.nodes.iterator.filter(dep_theories_set).toSet

                    val (nodes_status_changed, nodes_status1) =
                      st.nodes_status.update(resources.session_base, state, version,
                        domain = Some(domain), trim = changed.assignment)

                    if (nodes_status_delay >= Time.zero && nodes_status_changed) {
                      delay_nodes_status.invoke
                    }

                    val theory_progress =
                      (for {
                        (name, node_status) <- nodes_status1.present.iterator
                        if changed.nodes.contains(name) && !st.already_committed.isDefinedAt(name)
                        p1 = node_status.percentage
                        if p1 > 0 && Some(p1) != st.nodes_status.get(name).map(_.percentage)
                      } yield Progress.Theory(name.theory, percentage = Some(p1))).toList

                    (theory_progress, st.update(nodes_status1))
                  })

              theory_progress.foreach(progress.theory(_))

              check_result()

              if (commit.isDefined && commit_cleanup_delay > Time.zero) {
                if (use_theories_state.value.finished_result)
                  delay_commit_clean.revoke
                else delay_commit_clean.invoke
              }
            }
        }
      }

      try {
        session.commands_changed += consumer
        resources.load_theories(session, id, dep_theories, progress)
        use_theories_state.value.await_result
        check_progress.cancel
      }
      finally {
        session.commands_changed -= consumer
        resources.unload_theories(session, id, dep_theories)
      }

      use_theories_state.value.join_result
    }

    def purge_theories(
      theories: List[String],
      qualifier: String = Sessions.DRAFT,
      master_dir: String = "",
      all: Boolean = false): (List[Document.Node.Name], List[Document.Node.Name]) =
    {
      val nodes =
        if (all) None
        else Some(theories.map(resources.import_name(qualifier, master_directory(master_dir), _)))
      resources.purge_theories(session, nodes)
    }
  }


  /* internal state */

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

  sealed case class State(
    required: Multi_Map[Document.Node.Name, UUID] = Multi_Map.empty,
    theories: Map[Document.Node.Name, Theory] = Map.empty)
  {
    lazy val theory_graph: Graph[Document.Node.Name, Unit] =
    {
      val entries =
        for ((name, theory) <- theories.toList)
        yield ((name, ()), theory.node_header.imports.map(_._1).filter(theories.isDefinedAt(_)))
      Graph.make(entries, symmetric = true)(Document.Node.Name.Ordering)
    }

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

    def unload_theories(session: Session, id: UUID, dep_theories: List[Document.Node.Name]): State =
    {
      val st1 = remove_required(id, dep_theories)
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
    }

    def purge_theories(session: Session, nodes: List[Document.Node.Name])
      : ((List[Document.Node.Name], List[Document.Node.Name]), State) =
    {
      val all_nodes = theory_graph.topological_order
      val purge = nodes.filterNot(is_required(_)).toSet

      val retain = theory_graph.all_preds(all_nodes.filterNot(purge)).toSet
      val (retained, purged) = all_nodes.partition(retain)

      val purge_edits = purged.flatMap(name => theories(name).purge_edits)
      session.update(Document.Blobs.empty, purge_edits)

      ((purged, retained), remove_theories(purged))
    }

    def frontier_theories(clean: Set[Document.Node.Name]): Set[Document.Node.Name] =
    {
      @tailrec def frontier(base: List[Document.Node.Name], front: Set[Document.Node.Name])
        : Set[Document.Node.Name] =
      {
        val add = base.filter(b => theory_graph.imm_succs(b).forall(front))
        if (add.isEmpty) front
        else {
          val pre_add = add.map(theory_graph.imm_preds)
          val base1 = (pre_add.head /: pre_add.tail)(_ ++ _).toList.filter(clean)
          frontier(base1, front ++ add)
        }
      }
      frontier(theory_graph.maximals.filter(clean), Set.empty)
    }
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
    dep_theories: List[Document.Node.Name],
    progress: Progress)
  {
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

    val loaded = loaded_theories.length
    if (loaded > 1) progress.echo("Loading " + loaded + " theories ...")

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
  }

  def unload_theories(
    session: Thy_Resources.Session, id: UUID, dep_theories: List[Document.Node.Name])
  {
    state.change(_.unload_theories(session, id, dep_theories))
  }

  def clean_theories(session: Thy_Resources.Session, id: UUID, clean: Set[Document.Node.Name])
  {
    state.change(st =>
      {
        val frontier = st.frontier_theories(clean).toList
        if (frontier.isEmpty) st
        else {
          val st1 = st.unload_theories(session, id, frontier)
          val (_, st2) = st1.purge_theories(session, frontier)
          st2
        }
      })
  }

  def purge_theories(session: Thy_Resources.Session, nodes: Option[List[Document.Node.Name]])
    : (List[Document.Node.Name], List[Document.Node.Name]) =
  {
    state.change_result(st => st.purge_theories(session, nodes getOrElse st.theory_graph.keys))
  }
}
