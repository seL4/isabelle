/*  Title:      Pure/PIDE/headless.scala
    Author:     Makarius

Headless PIDE session and resources from file-system.
*/

package isabelle


import java.io.{File => JFile}

import scala.annotation.tailrec


object Headless {
  /** session **/

  private def stable_snapshot(
    state: Document.State,
    version: Document.Version,
    name: Document.Node.Name
  ): Document.Snapshot = {
    val snapshot = state.snapshot(name)
    assert(version.id == snapshot.version.id)
    snapshot
  }

  class Use_Theories_Result private[Headless](
    val state: Document.State,
    val version: Document.Version,
    val nodes: List[(Document.Node.Name, Document_Status.Node_Status)],
    val nodes_committed: List[(Document.Node.Name, Document_Status.Node_Status)]
  ) {
    def nodes_pending: List[(Document.Node.Name, Document_Status.Node_Status)] = {
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
    _resources: Headless.Resources)
  extends isabelle.Session {
    session =>

    override def session_options: Options = _session_options

    override def resources: Headless.Resources = _resources


    /* options */

    override def consolidate_delay: Time = session_options.seconds("headless_consolidate_delay")
    override def prune_delay: Time = session_options.seconds("headless_prune_delay")

    def default_check_delay: Time = session_options.seconds("headless_check_delay")
    def default_check_limit: Int = session_options.int("headless_check_limit")
    def default_nodes_status_delay: Time = session_options.seconds("headless_nodes_status_delay")
    def default_watchdog_timeout: Time = session_options.seconds("headless_watchdog_timeout")
    def default_commit_cleanup_delay: Time = session_options.seconds("headless_commit_cleanup_delay")

    def show_states: Boolean = session_options.bool("show_states")


    /* temporary directory */

    val tmp_dir: JFile = Isabelle_System.tmp_dir("server_session")
    val tmp_dir_name: String = File.path(tmp_dir).implode

    def master_directory(master_dir: String): String =
      proper_string(master_dir) getOrElse tmp_dir_name

    override def toString: String = session_name

    override def stop(): Process_Result = {
      try { super.stop() }
      finally { Isabelle_System.rm_tree(tmp_dir) }
    }


    /* theories */

    private object Load_State {
      def finished: Load_State = Load_State(Nil, Nil, Space.zero)

      def count_file(name: Document.Node.Name): Long =
        if (resources.loaded_theory(name)) 0 else File.size(name.path)
    }

    private case class Load_State(
      pending: List[Document.Node.Name],
      rest: List[Document.Node.Name],
      load_limit: Space
    ) {
      def next(
        dep_graph: Document.Node.Name.Graph[Unit],
        consolidated: Document.Node.Name => Boolean
      ): (List[Document.Node.Name], Load_State) = {
        def load_requirements(
          pending1: List[Document.Node.Name],
          rest1: List[Document.Node.Name]
        ) : (List[Document.Node.Name], Load_State) = {
          val load_theories = dep_graph.all_preds_rev(pending1)
          (load_theories, Load_State(pending1, rest1, load_limit))
        }

        if (!pending.forall(consolidated)) (Nil, this)
        else if (rest.isEmpty) (Nil, Load_State.finished)
        else if (!load_limit.is_proper) load_requirements(rest, Nil)
        else {
          val reachable =
            dep_graph.reachable_limit(
              load_limit.bytes, Load_State.count_file, dep_graph.imm_preds, rest)
          val (pending1, rest1) = rest.partition(reachable)
          load_requirements(pending1, rest1)
        }
      }
    }

    private sealed case class Use_Theories_State(
      dep_graph: Document.Node.Name.Graph[Unit],
      load_state: Load_State,
      watchdog_timeout: Time,
      commit: Option[(Document.Snapshot, Document_Status.Node_Status) => Unit],
      last_update: Time = Time.now(),
      nodes_status: Document_Status.Nodes_Status = Document_Status.Nodes_Status.empty,
      already_committed: Map[Document.Node.Name, Document_Status.Node_Status] = Map.empty,
      changed_nodes: Set[Document.Node.Name] = Set.empty,
      changed_assignment: Boolean = false,
      result: Option[Exn.Result[Use_Theories_Result]] = None
    ) {
      def nodes_status_update(state: Document.State, version: Document.Version,
        domain: Option[Set[Document.Node.Name]] = None,
        trim: Boolean = false
      ): (Boolean, Use_Theories_State) = {
        val nodes_status1 =
          nodes_status.update(resources, state, version, domain = domain, trim = trim)
        val st1 = copy(last_update = Time.now(), nodes_status = nodes_status1)
        (nodes_status1 != nodes_status, st1)
      }

      def changed(
        nodes: IterableOnce[Document.Node.Name],
        assignment: Boolean
      ): Use_Theories_State = {
        copy(
          changed_nodes = changed_nodes ++ nodes,
          changed_assignment = changed_assignment || assignment)
      }

      def reset_changed: Use_Theories_State =
        if (changed_nodes.isEmpty && !changed_assignment) this
        else copy(changed_nodes = Set.empty, changed_assignment = false)

      def watchdog: Boolean =
        watchdog_timeout > Time.zero && Time.now() - last_update > watchdog_timeout

      def finished_result: Boolean = result.isDefined

      def join_result: Option[(Exn.Result[Use_Theories_Result], Use_Theories_State)] =
        if (finished_result) Some((result.get, this)) else None

      def cancel_result: Use_Theories_State =
        if (finished_result) this else copy(result = Some(Exn.Exn(Exn.Interrupt())))

      def clean_theories: (List[Document.Node.Name], Use_Theories_State) = {
        @tailrec def frontier(
          base: List[Document.Node.Name],
          front: Set[Document.Node.Name]
        ) : Set[Document.Node.Name] = {
          val add = base.filter(name => dep_graph.imm_succs(name).forall(front))
          if (add.isEmpty) front
          else {
            val preds = add.map(dep_graph.imm_preds)
            val base1 =
              preds.tail.foldLeft(preds.head)(_ ++ _).toList.filter(already_committed.keySet)
            frontier(base1, front ++ add)
          }
        }

        if (already_committed.isEmpty) (Nil, this)
        else {
          val base =
            (for {
              (name, (_, (_, succs))) <- dep_graph.iterator
              if succs.isEmpty && already_committed.isDefinedAt(name)
            } yield name).toList
          val clean = frontier(base, Set.empty)
          if (clean.isEmpty) (Nil, this)
          else {
            (dep_graph.topological_order.filter(clean),
              copy(dep_graph = dep_graph.exclude(clean)))
          }
        }
      }

      private def consolidated(
        state: Document.State,
        version: Document.Version,
        name: Document.Node.Name
      ): Boolean = {
        resources.loaded_theory(name) ||
        nodes_status.quasi_consolidated(name) ||
        (if (commit.isDefined) already_committed.isDefinedAt(name)
         else state.node_consolidated(version, name))
      }

      def check(
        state: Document.State,
        version: Document.Version,
        beyond_limit: Boolean
      ) : (List[Document.Node.Name], Use_Theories_State) = {
        val st1 =
          commit match {
            case None => this
            case Some(commit_fn) =>
              copy(already_committed =
                dep_graph.topological_order.foldLeft(already_committed) {
                  case (committed, name) =>
                    def parents_committed: Boolean =
                      version.nodes(name).header.imports.forall(parent =>
                        resources.loaded_theory(parent) || committed.isDefinedAt(parent))
                    if (!committed.isDefinedAt(name) && parents_committed &&
                        state.node_consolidated(version, name)) {
                      val snapshot = stable_snapshot(state, version, name)
                      val status = Document_Status.Node_Status.make(state, version, name)
                      commit_fn(snapshot, status)
                      committed + (name -> status)
                    }
                    else committed
                })
          }

        def committed(name: Document.Node.Name): Boolean =
          resources.loaded_theory(name) || st1.already_committed.isDefinedAt(name)

        val (load_theories0, load_state1) =
          load_state.next(dep_graph, consolidated(state, version, _))

        val load_theories = load_theories0.filterNot(committed)

        val result1 = {
          val stopped = beyond_limit || watchdog
          if (!finished_result && load_theories.isEmpty &&
              (stopped || dep_graph.keys_iterator.forall(consolidated(state, version, _)))
          ) {
            @tailrec def make_nodes(
              input: List[Document.Node.Name],
              output: List[(Document.Node.Name, Document_Status.Node_Status)]
            ): Option[List[(Document.Node.Name, Document_Status.Node_Status)]] = {
              input match {
                case name :: rest =>
                  if (resources.loaded_theory(name)) make_nodes(rest, output)
                  else {
                    val status = Document_Status.Node_Status.make(state, version, name)
                    val ok = if (commit.isDefined) committed(name) else status.consolidated
                    if (stopped || ok) make_nodes(rest, (name -> status) :: output) else None
                  }
                case Nil => Some(output)
              }
            }

            for (nodes <- make_nodes(dep_graph.topological_order.reverse, Nil)) yield {
              val nodes_committed =
                (for {
                  name <- dep_graph.keys_iterator
                  status <- st1.already_committed.get(name)
                } yield name -> status).toList
              Exn.Res(new Use_Theories_Result(state, version, nodes, nodes_committed))
            }
          }
          else result
        }

        (load_theories, st1.copy(result = result1, load_state = load_state1))
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
      // commit: must not block, must not fail
      commit: Option[(Document.Snapshot, Document_Status.Node_Status) => Unit] = None,
      commit_cleanup_delay: Time = default_commit_cleanup_delay,
      progress: Progress = new Progress
    ): Use_Theories_Result = {
      val dependencies = {
        val import_names =
          theories.map(thy =>
            resources.import_name(qualifier, master_directory(master_dir), thy) -> Position.none)
        resources.dependencies(import_names, progress = progress).check_errors
      }
      val dep_theories = dependencies.theories
      val dep_theories_set = dep_theories.toSet
      val dep_files = dependencies.loaded_files

      val use_theories_state = {
        val dep_graph = dependencies.theory_graph

        val maximals = dep_graph.maximals
        val rest =
          if (maximals.isEmpty || maximals.tail.isEmpty) maximals
          else {
            val depth = dep_graph.node_depth(Load_State.count_file)
            maximals.sortBy(node => - depth(node))
          }
        val load_limit =
          if (commit.isDefined) Space.MiB(session_options.real("headless_load_limit"))
          else Space.zero
        val load_state = Load_State(Nil, rest, load_limit)

        Synchronized(Use_Theories_State(dep_graph, load_state, watchdog_timeout, commit))
      }

      def check_state(
        beyond_limit: Boolean = false,
        state: Document.State = session.get_state()
      ): Unit = {
        for {
          version <- state.stable_tip_version
          load_theories = use_theories_state.change_result(_.check(state, version, beyond_limit))
          if load_theories.nonEmpty
        } resources.load_theories(session, id, load_theories, dep_files, unicode_symbols, progress)
      }

      lazy val check_progress = {
        var check_count = 0
        Event_Timer.request(Time.now(), repeat = Some(check_delay)) {
          if (progress.stopped) use_theories_state.change(_.cancel_result)
          else {
            check_count += 1
            check_state(check_limit > 0 && check_count > check_limit)
          }
        }
      }

      val consumer = {
        val delay_nodes_status =
          Delay.first(nodes_status_delay max Time.zero) {
            val st = use_theories_state.value
            progress.nodes_status(st.dep_graph.topological_order, st.nodes_status)
          }

        val delay_commit_clean =
          Delay.first(commit_cleanup_delay max Time.zero) {
            val clean_theories = use_theories_state.change_result(_.clean_theories)
            if (clean_theories.nonEmpty && session.is_ready) {
              progress.echo("Removing " + clean_theories.length + " theories ...")
              resources.clean_theories(session, id, clean_theories)
            }
          }

        isabelle.Session.Consumer[isabelle.Session.Commands_Changed](getClass.getName) { changed =>
          val state = session.get_state()

          def apply_changed(st: Use_Theories_State): Use_Theories_State =
            st.changed(changed.nodes.iterator.filter(dep_theories_set), changed.assignment)

          state.stable_tip_version match {
            case None => use_theories_state.change(apply_changed)
            case Some(version) =>
              val theory_progress =
                use_theories_state.change_result { st =>
                  val changed_st = apply_changed(st)

                  val domain =
                    if (st.nodes_status.is_empty) dep_theories_set
                    else changed_st.changed_nodes

                  val (nodes_status_changed, st1) =
                    st.reset_changed.nodes_status_update(state, version,
                      domain = Some(domain), trim = changed_st.changed_assignment)

                  if (nodes_status_delay >= Time.zero && nodes_status_changed) {
                    delay_nodes_status.invoke()
                  }

                  val theory_progress =
                    (for {
                      name <- st1.dep_graph.topological_order.iterator
                      node_status = st1.nodes_status(name)
                      if !node_status.is_empty && changed_st.changed_nodes(name) &&
                        !st.already_committed.isDefinedAt(name)
                      p1 = node_status.percentage
                      if p1 > 0 && !st.nodes_status.get(name).map(_.percentage).contains(p1)
                    } yield Progress.Theory(name.theory, percentage = Some(p1))).toList

                  if (commit.isDefined && commit_cleanup_delay > Time.zero) {
                    if (st1.finished_result) delay_commit_clean.revoke()
                    else delay_commit_clean.invoke()
                  }

                  (theory_progress, st1)
                }

              theory_progress.foreach(progress.theory)

              check_state(state = state)
          }
        }
      }

      try {
        session.commands_changed += consumer
        check_progress
        use_theories_state.guarded_access(_.join_result)
        check_progress.cancel()
      }
      finally {
        session.commands_changed -= consumer
        resources.unload_theories(session, id, dep_theories)
      }

      Exn.release(use_theories_state.guarded_access(_.join_result))
    }

    def purge_theories(
      theories: List[String],
      qualifier: String = Sessions.DRAFT,
      master_dir: String = "",
      all: Boolean = false
    ): (List[Document.Node.Name], List[Document.Node.Name]) = {
      val nodes =
        if (all) None
        else Some(theories.map(resources.import_name(qualifier, master_directory(master_dir), _)))
      resources.purge_theories(nodes)
    }
  }



  /** resources **/

  object Resources {
    def apply(
      options: Options,
      session_background: Sessions.Background,
      log: Logger = new Logger
    ): Resources = new Resources(options, session_background, log = log)

    def make(
      options: Options,
      session_name: String,
      session_dirs: List[Path] = Nil,
      include_sessions: List[String] = Nil,
      progress: Progress = new Progress,
      log: Logger = new Logger
    ): Resources = {
      val session_background =
        Sessions.background(options, session_name, dirs = session_dirs,
          include_sessions = include_sessions, progress = progress)
      apply(options, session_background, log = log)
    }

    final class Theory private[Headless](
      val node_name: Document.Node.Name,
      val node_header: Document.Node.Header,
      val text: String,
      val node_required: Boolean
    ) {
      override def toString: String = node_name.toString

      def node_perspective: Document.Node.Perspective_Text.T =
        Document.Node.Perspective(node_required, Text.Perspective.empty, Document.Node.Overlays.empty)

      def make_edits(text_edits: List[Text.Edit]): List[Document.Edit_Text] =
        List(node_name -> Document.Node.Deps(node_header),
          node_name -> Document.Node.Edits(text_edits),
          node_name -> node_perspective)

      def node_edits(old: Option[Theory]): List[Document.Edit_Text] = {
        val (text_edits, old_required) =
          if (old.isEmpty) (Text.Edit.inserts(0, text), false)
          else (Text.Edit.replace(0, old.get.text, text), old.get.node_required)

        if (text_edits.isEmpty && node_required == old_required) Nil
        else make_edits(text_edits)
      }

      def purge_edits: List[Document.Edit_Text] =
        make_edits(Text.Edit.removes(0, text))

      def set_required(required: Boolean): Theory =
        if (required == node_required) this
        else new Theory(node_name, node_header, text, required)
    }

    sealed case class State(
      blobs: Map[Document.Node.Name, Document.Blobs.Item] = Map.empty,
      theories: Map[Document.Node.Name, Theory] = Map.empty,
      required: Multi_Map[Document.Node.Name, UUID.T] = Multi_Map.empty
    ) {
      /* blobs */

      def doc_blobs: Document.Blobs = Document.Blobs(blobs)

      def update_blobs(names: List[Document.Node.Name]): (Document.Blobs, State) = {
        val new_blobs =
          names.flatMap { name =>
            val bytes = Bytes.read(name.path)
            blobs.get(name) match {
              case Some(blob) if blob.bytes == bytes => None
              case _ =>
                val text = bytes.text
                val blob = Document.Blobs.Item(bytes, text, Symbol.Text_Chunk(text), changed = true)
                Some(name -> blob)
            }
          }
        val blobs1 = new_blobs.foldLeft(blobs)(_ + _)
        val blobs2 = new_blobs.foldLeft(blobs) { case (map, (a, b)) => map + (a -> b.unchanged) }
        (Document.Blobs(blobs1), copy(blobs = blobs2))
      }

      def blob_edits(
        name: Document.Node.Name,
        old_blob: Option[Document.Blobs.Item]
      ) : List[Document.Edit_Text] = {
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

      lazy val theory_graph: Document.Node.Name.Graph[Unit] =
        Document.Node.Name.make_graph(
          for ((name, theory) <- theories.toList)
          yield ((name, ()), theory.node_header.imports.filter(theories.isDefinedAt)))

      def is_required(name: Document.Node.Name): Boolean = required.isDefinedAt(name)

      def insert_required(id: UUID.T, names: List[Document.Node.Name]): State =
        copy(required = names.foldLeft(required)(_.insert(_, id)))

      def remove_required(id: UUID.T, names: List[Document.Node.Name]): State =
        copy(required = names.foldLeft(required)(_.remove(_, id)))

      def update_theories(update: List[Theory]): State =
        copy(theories =
          update.foldLeft(theories) {
            case (thys, thy) =>
              thys.get(thy.node_name) match {
                case Some(thy1) if thy1 == thy => thys
                case _ => thys + (thy.node_name -> thy)
              }
          })

      def remove_theories(remove: List[Document.Node.Name]): State = {
        require(remove.forall(name => !is_required(name)), "attempt to remove required nodes")
        copy(theories = theories -- remove)
      }

      def unload_theories(
        id: UUID.T,
        theories: List[Document.Node.Name]
      ) : (List[Document.Edit_Text], State) = {
        val st1 = remove_required(id, theories)
        val theory_edits =
          for {
            node_name <- theories
            theory <- st1.theories.get(node_name)
          }
          yield {
            val theory1 = theory.set_required(st1.is_required(node_name))
            val edits = theory1.node_edits(Some(theory))
            (theory1, edits)
          }
        (theory_edits.flatMap(_._2), st1.update_theories(theory_edits.map(_._1)))
      }

      def purge_theories(
        nodes: Option[List[Document.Node.Name]]
      ) : ((List[Document.Node.Name], List[Document.Node.Name], List[Document.Edit_Text]), State) = {
        val all_nodes = theory_graph.topological_order
        val purge = nodes.getOrElse(all_nodes).filterNot(is_required).toSet

        val retain = theory_graph.all_preds(all_nodes.filterNot(purge)).toSet
        val (retained, purged) = all_nodes.partition(retain)
        val purge_edits = purged.flatMap(name => theories(name).purge_edits)

        ((purged, retained, purge_edits), remove_theories(purged))
      }
    }
  }

  class Resources private[Headless](
    val options: Options,
    session_background: Sessions.Background,
    log: Logger = new Logger)
  extends isabelle.Resources(session_background.check_errors, log = log) {
    resources =>

    val store: Store = Store(options)


    /* session */

    def start_session(
      print_mode: List[String] = Nil,
      progress: Progress = new Progress
    ): Session = {
      val session_name = session_background.session_name
      val session = new Session(session_name, options, resources)

      val session_heaps = store.session_heaps(session_background, logic = session_name)

      progress.echo("Starting session " + session_name + " ...")
      Isabelle_Process.start(
        options, session, session_background, session_heaps, modes = print_mode).await_startup()

      session
    }


    /* theories */

    private val state = Synchronized(Resources.State())

    def load_theories(
      session: Session,
      id: UUID.T,
      theories: List[Document.Node.Name],
      files: List[Document.Node.Name],
      unicode_symbols: Boolean,
      progress: Progress
    ): Unit = {
      val loaded_theories =
        for (node_name <- theories)
        yield {
          val path = node_name.path
          if (!node_name.is_theory) error("Not a theory file: " + path)

          progress.expose_interrupt()
          val text = Symbol.output(unicode_symbols, File.read(path))
          val node_header = resources.check_thy(node_name, Scan.char_reader(text))
          new Resources.Theory(node_name, node_header, text, true)
        }

      val loaded = loaded_theories.length
      if (loaded > 1) progress.echo("Loading " + loaded + " theories ...")

      state.change { st =>
        val (doc_blobs1, st1) = st.insert_required(id, theories).update_blobs(files)
        val theory_edits =
          for (theory <- loaded_theories)
          yield {
            val node_name = theory.node_name
            val old_theory = st.theories.get(node_name)
            val theory1 = theory.set_required(st1.is_required(node_name))
            val edits = theory1.node_edits(old_theory)
            (theory1, edits)
          }
        val file_edits =
          for { node_name <- files if doc_blobs1.changed(node_name) }
          yield st1.blob_edits(node_name, st.blobs.get(node_name))

        session.update(doc_blobs1, theory_edits.flatMap(_._2) ::: file_edits.flatten)
        st1.update_theories(theory_edits.map(_._1))
      }
    }

    def unload_theories(session: Session, id: UUID.T, theories: List[Document.Node.Name]): Unit = {
      state.change { st =>
        val (edits, st1) = st.unload_theories(id, theories)
        session.update(st.doc_blobs, edits)
        st1
      }
    }

    def clean_theories(session: Session, id: UUID.T, theories: List[Document.Node.Name]): Unit = {
      state.change { st =>
        val (edits1, st1) = st.unload_theories(id, theories)
        val ((_, _, edits2), st2) = st1.purge_theories(None)
        session.update(st.doc_blobs, edits1 ::: edits2)
        st2
      }
    }

    def purge_theories(
      nodes: Option[List[Document.Node.Name]]
    ) : (List[Document.Node.Name], List[Document.Node.Name]) = {
      state.change_result { st =>
        val ((purged, retained, _), st1) = st.purge_theories(nodes)
        ((purged, retained), st1)
      }
    }
  }
}
