/*  Title:      Pure/PIDE/headless.scala
    Author:     Makarius

Headless PIDE session and resources from file-system.
*/

package isabelle


import java.io.{File => JFile}

import scala.annotation.tailrec
import scala.collection.mutable


object Headless
{
  /** session **/

  private def stable_snapshot(
    state: Document.State, version: Document.Version, name: Document.Node.Name): Document.Snapshot =
  {
    val snapshot = state.snapshot(name)
    assert(version.id == snapshot.version.id)
    snapshot
  }

  class Use_Theories_Result private[Headless](
    val state: Document.State,
    val version: Document.Version,
    val nodes: List[(Document.Node.Name, Document_Status.Node_Status)],
    val nodes_committed: List[(Document.Node.Name, Document_Status.Node_Status)])
  {
    def nodes_pending: List[(Document.Node.Name, Document_Status.Node_Status)] =
    {
      val committed = nodes_committed.iterator.map(_._1).toSet
      nodes.filter(p => !committed(p._1))
    }

    def snapshot(name: Document.Node.Name): Document.Snapshot =
      stable_snapshot(state, version, name)

    def ok: Boolean =
      (nodes.iterator ++ nodes_committed.iterator).forall({ case (_, st) => st.ok })
  }

  class Session private[Headless](
    session_name: String,
    _session_options: => Options,
    override val resources: Resources) extends isabelle.Session(_session_options, resources)
  {
    session =>


    /* options */

    def default_check_delay: Time = session_options.seconds("headless_check_delay")
    def default_check_limit: Int = session_options.int("headless_check_limit")
    def default_nodes_status_delay: Time = session_options.seconds("headless_nodes_status_delay")
    def default_watchdog_timeout: Time = session_options.seconds("headless_watchdog_timeout")
    def default_commit_cleanup_delay: Time = session_options.seconds("headless_commit_cleanup_delay")


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
      result: Promise[Use_Theories_Result] = Future.promise[Use_Theories_Result])
    {
      def update(new_nodes_status: Document_Status.Nodes_Status): Use_Theories_State =
        copy(last_update = Time.now(), nodes_status = new_nodes_status)

      def watchdog(watchdog_timeout: Time): Boolean =
        watchdog_timeout > Time.zero && Time.now() - last_update > watchdog_timeout

      def cancel_result { result.cancel }
      def finished_result: Boolean = result.is_finished
      def await_result { result.join_result }
      def join_result: Use_Theories_Result = result.join
      def check_result(
          state: Document.State,
          version: Document.Version,
          dep_theories: List[Document.Node.Name],
          beyond_limit: Boolean,
          watchdog_timeout: Time,
          commit: Option[(Document.Snapshot, Document_Status.Node_Status) => Unit])
        : Use_Theories_State =
      {
        val already_committed1 =
          if (commit.isDefined) {
            (already_committed /: dep_theories)({ case (committed, name) =>
              def parents_committed: Boolean =
                version.nodes(name).header.imports.forall({ case (parent, _) =>
                  resources.session_base.loaded_theory(parent) || committed.isDefinedAt(parent)
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
          }
          else already_committed

        if (beyond_limit || watchdog(watchdog_timeout) ||
          dep_theories.forall(name =>
            already_committed1.isDefinedAt(name) ||
            state.node_consolidated(version, name) ||
            nodes_status.quasi_consolidated(name)))
        {
          val nodes =
            for (name <- dep_theories)
            yield { (name -> Document_Status.Node_Status.make(state, version, name)) }
          val nodes_committed =
            for {
              name <- dep_theories
              status <- already_committed1.get(name)
            } yield (name -> status)

          try { result.fulfill(new Use_Theories_Result(state, version, nodes, nodes_committed)) }
          catch { case _: IllegalStateException => }
        }

        copy(already_committed = already_committed1)
      }
    }

    def use_theories(
      theories: List[String],
      qualifier: String = Sessions.DRAFT,
      master_dir: String = "",
      unicode_symbols: Boolean = false,
      check_delay: Time = default_check_delay,
      check_limit: Int = default_check_limit,
      watchdog_timeout: Time = default_watchdog_timeout,
      nodes_status_delay: Time = default_nodes_status_delay,
      id: UUID.T = UUID.random(),
      share_common_data: Boolean = false,
      // commit: must not block, must not fail
      commit: Option[(Document.Snapshot, Document_Status.Node_Status) => Unit] = None,
      commit_cleanup_delay: Time = default_commit_cleanup_delay,
      progress: Progress = No_Progress): Use_Theories_Result =
    {
      val dependencies =
      {
        val import_names =
          theories.map(thy =>
            resources.import_name(qualifier, master_directory(master_dir), thy) -> Position.none)
        resources.dependencies(import_names, progress = progress).check_errors
      }
      val dep_theories = dependencies.theories
      val dep_files =
        dependencies.loaded_files(false).flatMap(_._2).
          map(path => Document.Node.Name(resources.append("", path)))

      val use_theories_state = Synchronized(Use_Theories_State())

      def check_result_state(beyond_limit: Boolean = false)
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
              check_result_state(check_limit > 0 && check_count > check_limit)
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
                      st.nodes_status.update(resources, state, version,
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

              check_result_state()

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
        resources.load_theories(
          session, id, dep_theories, dep_files, unicode_symbols, share_common_data, progress)
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



  /** resources **/

  object Resources
  {
    def apply(base_info: Sessions.Base_Info, log: Logger = No_Logger): Resources =
      new Resources(base_info, log = log)

    def make(
      options: Options,
      session_name: String,
      session_dirs: List[Path] = Nil,
      include_sessions: List[String] = Nil,
      progress: Progress = No_Progress,
      log: Logger = No_Logger): Resources =
    {
      val base_info =
        Sessions.base_info(options, session_name, dirs = session_dirs,
          include_sessions = include_sessions, progress = progress)
      apply(base_info, log = log)
    }

    final class Theory private[Headless](
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
      blobs: Map[Document.Node.Name, Document.Blob] = Map.empty,
      theories: Map[Document.Node.Name, Theory] = Map.empty,
      required: Multi_Map[Document.Node.Name, UUID.T] = Multi_Map.empty)
    {
      /* blobs */

      def doc_blobs: Document.Blobs = Document.Blobs(blobs)

      def update_blobs(names: List[Document.Node.Name]): (Document.Blobs, State) =
      {
        val new_blobs =
          names.flatMap(name =>
          {
            val bytes = Bytes.read(name.path)
            def new_blob: Document.Blob =
            {
              val text = bytes.text
              Document.Blob(bytes, text, Symbol.Text_Chunk(text), changed = true)
            }
            blobs.get(name) match {
              case Some(blob) => if (blob.bytes == bytes) None else Some(name -> new_blob)
              case None => Some(name -> new_blob)
            }
          })
        val blobs1 = (blobs /: new_blobs)(_ + _)
        val blobs2 = (blobs /: new_blobs)({ case (map, (a, b)) => map + (a -> b.unchanged) })
        (Document.Blobs(blobs1), copy(blobs = blobs2))
      }

      def blob_edits(name: Document.Node.Name, old_blob: Option[Document.Blob])
        : List[Document.Edit_Text] =
      {
        val blob = blobs.getOrElse(name, error("Missing blob " + quote(name.toString)))
        val text_edits =
          old_blob match {
            case None => List(Text.Edit.insert(0, blob.source))
            case Some(blob0) => Text.Edit.replace(0, blob0.source, blob.source)
          }
        if (text_edits.isEmpty) Nil
        else List(name -> Document.Node.Blob(blob), name -> Document.Node.Edits(text_edits))
      }


      /* theories */

      lazy val theory_graph: Graph[Document.Node.Name, Unit] =
      {
        val entries =
          for ((name, theory) <- theories.toList)
          yield ((name, ()), theory.node_header.imports.map(_._1).filter(theories.isDefinedAt(_)))
        Graph.make(entries, symmetric = true)(Document.Node.Name.Ordering)
      }

      def is_required(name: Document.Node.Name): Boolean = required.isDefinedAt(name)

      def insert_required(id: UUID.T, names: List[Document.Node.Name]): State =
        copy(required = (required /: names)(_.insert(_, id)))

      def remove_required(id: UUID.T, names: List[Document.Node.Name]): State =
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

      def unload_theories(session: Session, id: UUID.T, dep_theories: List[Document.Node.Name])
        : State =
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
        session.update(doc_blobs, theory_edits.flatMap(_._1))
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
        session.update(doc_blobs, purge_edits)

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

  class Resources private[Headless](
      val session_base_info: Sessions.Base_Info,
      log: Logger = No_Logger)
    extends isabelle.Resources(session_base_info.check_base, log = log)
  {
    resources =>

    def options: Options = session_base_info.options


    /* dependencies */

    def used_theories(
      deps: Sessions.Deps, progress: Progress = No_Progress): List[Document.Node.Name] =
    {
      for {
        name <- deps.used_theories_condition(options, progress = progress).topological_order
        if !session_base.loaded_theory(name.theory)
      } yield name
    }


    /* session */

    def start_session(print_mode: List[String] = Nil, progress: Progress = No_Progress): Session =
    {
      val session = new Session(session_base_info.session, options, resources)

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

      progress.echo("Starting session " + session_base_info.session + " ...")
      Isabelle_Process.start(session, options,
        logic = session_base_info.session, dirs = session_base_info.dirs, modes = print_mode)

      session_error.join match {
        case "" => session
        case msg => session.stop(); error(msg)
      }
    }


    /* theories */

    private val state = Synchronized(Resources.State())

    def load_theories(
      session: Session,
      id: UUID.T,
      dep_theories: List[Document.Node.Name],
      dep_files: List[Document.Node.Name],
      unicode_symbols: Boolean,
      share_common_data: Boolean,
      progress: Progress)
    {
      val loaded_theories =
        for (node_name <- dep_theories)
        yield {
          val path = node_name.path
          if (!node_name.is_theory) error("Not a theory file: " + path)

          progress.expose_interrupt()
          val text0 = File.read(path)
          val text = if (unicode_symbols) Symbol.decode(text0) else text0
          val node_header = resources.check_thy_reader(node_name, Scan.char_reader(text))
          new Resources.Theory(node_name, node_header, text, true)
        }

      val loaded = loaded_theories.length
      if (loaded > 1) progress.echo("Loading " + loaded + " theories ...")

      state.change(st =>
        {
          val (doc_blobs1, st1) = st.insert_required(id, dep_theories).update_blobs(dep_files)
          val theory_edits =
            for (theory <- loaded_theories)
            yield {
              val node_name = theory.node_name
              val theory1 = theory.required(st1.is_required(node_name))
              val edits = theory1.node_edits(st1.theories.get(node_name))
              (edits, (node_name, theory1))
            }
          val file_edits =
            for { node_name <- dep_files if doc_blobs1.changed(node_name) }
            yield st1.blob_edits(node_name, st.blobs.get(node_name))

          session.update(doc_blobs1, theory_edits.flatMap(_._1) ::: file_edits.flatten,
            share_common_data = share_common_data)
          st1.update_theories(theory_edits.map(_._2))
        })
    }

    def unload_theories(session: Session, id: UUID.T, dep_theories: List[Document.Node.Name])
    {
      state.change(_.unload_theories(session, id, dep_theories))
    }

    def clean_theories(session: Session, id: UUID.T, clean: Set[Document.Node.Name])
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

    def purge_theories(session: Session, nodes: Option[List[Document.Node.Name]])
      : (List[Document.Node.Name], List[Document.Node.Name]) =
    {
      state.change_result(st => st.purge_theories(session, nodes getOrElse st.theory_graph.keys))
    }
  }
}
